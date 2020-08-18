import logging
import operator
from abc import abstractmethod
from fractions import Fraction
from math import floor, ceil
from typing import List, Sequence, Any, Dict, Optional, Iterable, Tuple

import sympy as sym
import statsmodels.api as sm  # type: ignore
import pandas as pd  # type: ignore
import numpy as np  # type: ignore
import scipy.stats as st  # type: ignore

from mockdown.constraint import IConstraint
from mockdown.learning.noisetolerant.types import NoiseTolerantLearningConfig
from mockdown.types import unopt
from mockdown.learning.types import IConstraintLearning, ConstraintCandidate
from mockdown.model import IView

logger = logging.getLogger(__name__)


class NoiseTolerantLearning(IConstraintLearning):
    def __init__(self,
                 templates: Sequence[IConstraint],
                 samples: List[IView[sym.Number]],
                 config: Optional[NoiseTolerantLearningConfig] = None) -> None:
        self.templates = [tpl for tpl in templates if tpl.op is operator.eq]
        self.samples = samples

        if not config:
            config = NoiseTolerantLearningConfig(sample_count=len(samples))
        self.config = config

    def learn(self) -> List[List[ConstraintCandidate]]:
        def gen_candidates() -> Iterable[List[ConstraintCandidate]]:
            for template in self.templates:
                data = self.find_template_data(template)

                task: NoiseTolerantTemplateModel
                if template.kind.is_constant_form:
                    task = NoiseTolerantConstantTemplateModel(template, data, self.config)
                else:
                    task = NoiseTolerantLinearTemplateModel(template, data, self.config)

                if task.reject():
                    yield []
                else:
                    yield task.learn()

        return list(gen_candidates())

    def find_template_data(self, template: IConstraint) -> pd.DataFrame:
        """Extract the data for a given template from the samples."""
        if template.kind.is_constant_form:
            columns = [template.y_id]
        else:
            columns = [template.y_id, unopt(template.x_id)]

        rows = []
        for sample in self.samples:
            rows.append([unopt(sample.find_anchor(col)).value for col in columns])

        return pd.DataFrame(rows, columns=list(map(str, columns)), dtype=np.float)


class NoiseTolerantTemplateModel:
    def __init__(self, template: IConstraint, data: pd.DataFrame, config: NoiseTolerantLearningConfig):
        self.template = template
        self.data = data
        self.config = config

    @property
    def x_name(self) -> str:
        return str(self.template.x_id)

    @property
    def y_name(self) -> str:
        return str(self.template.y_id)

    @property
    def x_data(self) -> pd.DataFrame:
        return self.data[self.x_name]

    @property
    def y_data(self) -> pd.DataFrame:
        return self.data[self.y_name]

    @abstractmethod
    def learn(self) -> List[ConstraintCandidate]: ...

    @abstractmethod
    def reject(self) -> bool: ...

    @abstractmethod
    def a_bounds(self) -> Tuple[Fraction, Fraction]: ...

    @abstractmethod
    def b_bounds(self) -> Tuple[int, int]: ...


class NoiseTolerantConstantTemplateModel(NoiseTolerantTemplateModel):
    def learn(self) -> List[ConstraintCandidate]:
        return []

    def reject(self) -> bool:
        y_data = self.y_data

        # Is the variance of residuals small enough?
        rstd = np.std(y_data - np.mean(y_data)).item()
        if rstd > self.config.cutoff_spread:
            logger.info(
                f"REJECTED `{self.template}`, stdev of residuals too high: {rstd} > {self.config.cutoff_spread}")
            logger.debug(f"Data:\n{self.data}")
            return True

        logger.debug(f"ACCEPTED `{self.template}`")
        logger.debug(f"Bounds: "
                     f"a ∈ [{self.a_bounds()[0]}, {self.a_bounds()[1]}], "
                     f"b ∈ [{self.b_bounds()[0]}, {self.b_bounds()[1]}]")
        logger.debug(f"Data:\n{self.data}")
        return False

    def a_bounds(self) -> Tuple[Fraction, Fraction]:
        return Fraction(1), Fraction(1)

    def b_bounds(self) -> Tuple[int, int]:
        y, alpha, n = self.y_data, self.config.b_alpha, self.config.sample_count
        y_mu = np.mean(y)

        t = np.abs(st.t.ppf(alpha / 2, n - 2))
        sem = st.sem(y)
        return y_mu - t * sem, y_mu + t * sem


class NoiseTolerantLinearTemplateModel(NoiseTolerantTemplateModel):
    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self.model = sm.OLS(self.y_data, sm.add_constant(self.x_data))
        self.fit = self.model.fit()

    def learn(self) -> List[ConstraintCandidate]:
        return []

    def reject(self) -> bool:
        x, y = self.x_data, self.y_data

        if np.var(x) == 0:
            if np.std(y) < self.config.cutoff_spread:
                logger.debug(f"ACCEPTED `{self.template}`")
                logger.debug(f"Bounds: "
                             f"a ∈ [{self.a_bounds()[0]}, {self.a_bounds()[1]}], "
                             f"b ∈ [{self.b_bounds()[0]}, {self.b_bounds()[1]}]")
                logger.debug(f"Data:\n{self.data}")
                return False
            logger.info(
                f"REJECTED `{self.template}`, no x variance and stdev of y is too high: "
                f"{np.std(y)} > {self.config.cutoff_spread}")
            logger.debug(f"Data:\n{self.data}")
            return True

        if np.var(y) == 0:
            if np.std(x) < self.config.cutoff_spread:
                logger.debug(f"ACCEPTED `{self.template}`")
                logger.debug(f"Bounds: "
                             f"a ∈ [{self.a_bounds()[0]}, {self.a_bounds()[1]}], "
                             f"b ∈ [{self.b_bounds()[0]}, {self.b_bounds()[1]}]")
                logger.debug(f"Data:\n{self.data}")
                return False
            logger.info(
                f"REJECTED `{self.template}`, no y variance and stdev of x is too high: "
                f"{np.std(x)} > {self.config.cutoff_spread}")
            logger.debug(f"Data:\n{self.data}")
            return True

        # Do we fail to reject the null-hypothesis that the slope is 0?
        wald_res = self.fit.wald_test(np.eye(2))
        if not wald_res.pvalue < self.config.cutoff_fit:
            logger.info(f"REJECTED `{self.template}`, Wald test failed to reject H0 (a=b=0): "
                        f"(p = {wald_res.pvalue} ≥ {self.config.cutoff_fit})")
            logger.debug(f"Data:\n{self.data}")
            return True

        # Are the residuals small?
        resid_std = np.std(self.fit.resid)
        if resid_std > self.config.cutoff_spread:
            logger.info(
                f"REJECTED `{self.template}`, stdev of residuals too high: {resid_std} > {self.config.cutoff_spread}")
            logger.debug(f"Data:\n{self.data}")
            return True

        # Does the data's slope appear negative?
        # todo: is this necessary?
        if self.fit.rsquared < 0:
            logger.info(f"REJECTED `{self.template}`, slope is negative.")
            logger.debug(f"LinReg summary: {self.fit}")
            logger.debug(f"Data:\n{self.data}")
            return True

        logger.debug(f"ACCEPTED `{self.template}`")
        logger.debug(f"Bounds: "
                     f"a ∈ [{self.a_bounds()[0]}, {self.a_bounds()[1]}], "
                     f"b ∈ [{self.b_bounds()[0]}, {self.b_bounds()[1]}]")
        logger.debug(f"Data:\n{self.data}")
        return False

    def a_bounds(self) -> Tuple[Fraction, Fraction]:
        if self.template.kind.is_add_only_form:
            return Fraction(1), Fraction(1)
        else:
            max_d = self.config.max_denominator
            al, au = self.fit.conf_int().iloc[1]
            return Fraction(al).limit_denominator(max_d), Fraction(au).limit_denominator(max_d)

    def b_bounds(self) -> Tuple[int, int]:
        if self.template.kind.is_mul_only_form:
            return 0, 0
        else:
            bl, bu = self.fit.conf_int().iloc[0]
            return floor(bl), ceil(bu)
