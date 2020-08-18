import logging
import operator
from abc import abstractmethod
from typing import List, Sequence, Any, Dict, Optional, Iterable

import sympy as sym
import statsmodels.api as sm  # type: ignore
import pandas as pd  # type: ignore
import numpy as np  # type: ignore
import scipy.stats as st  # type: ignore

from mockdown.constraint import IConstraint
from mockdown.learning.fancy.types import FancyLearningConfig
from mockdown.types import unopt
from mockdown.learning.types import IConstraintLearning, ConstraintCandidate
from mockdown.model import IView

logger = logging.getLogger(__name__)


class FancyLearning(IConstraintLearning):
    def __init__(self,
                 templates: Sequence[IConstraint],
                 samples: List[IView[sym.Number]],
                 config: Optional[FancyLearningConfig] = None) -> None:
        self.templates = [tpl for tpl in templates if tpl.op is operator.eq]
        self.samples = samples

        if not config:
            config = FancyLearningConfig(sample_count=len(samples))
        self.config = config

    def learn(self) -> List[List[ConstraintCandidate]]:
        def gen_candidates() -> Iterable[List[ConstraintCandidate]]:
            for template in self.templates:
                data = self.find_template_data(template)

                task: FancyTemplateLearning
                if template.kind.is_constant_form:
                    task = FancyConstantTemplateLearning(template, data, self.config)
                else:
                    task = FancyLinearTemplateLearning(template, data, self.config)

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


class FancyTemplateLearning:
    def __init__(self, template: IConstraint, data: pd.DataFrame, config: FancyLearningConfig):
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


class FancyConstantTemplateLearning(FancyTemplateLearning):
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
        logger.debug(f"Data:\n{self.data}")
        return False


class FancyLinearTemplateLearning(FancyTemplateLearning):
    def learn(self) -> List[ConstraintCandidate]:
        return []

    def reject(self) -> bool:
        x, y = self.x_data, self.y_data

        if np.var(x) == 0:
            if np.std(y) < self.config.cutoff_spread:
                logger.debug(f"ACCEPTED `{self.template}`")
                logger.debug(f"Data:\n{self.data}")
                return False
            logger.info(
                f"REJECTED `{self.template}`, no x variance and stdev of y is too high: "
                f"{np.std(y)} > {self.config.cutoff_spread}")
            logger.debug(f"Data:\n{self.data}")
            return True

        a, b, r, p, std = st.linregress(self.x_data, self.y_data)

        # Do we fail to reject the null-hypothesis that the slope is 0?
        if not p < self.config.cutoff_fit:
            logger.info(f"REJECTED `{self.template}`, failed linear-regression Wald test: "
                        f"(p = {p} ≥ {self.config.cutoff_fit})")
            logger.debug(f"Data:\n{self.data}")
            return True

        # Are the residuals small?
        res = np.std(y - a * x + b)
        rstd = np.std(res)
        if rstd > self.config.cutoff_spread:
            logger.info(
                f"REJECTED `{self.template}`, stdev of residuals too high: {rstd} > {self.config.cutoff_spread}")
            logger.debug(f"Data:\n{self.data}")
            return True

        # Does the data's slope appear negative?
        # todo: is this necessary?
        if r < 0:
            logger.info(f"REJECTED `{self.template}`, slope is negative.")
            logger.debug(f"LinReg summary: a={a}, b={b}, p={p}, r={r}, std={std}")
            logger.debug(f"Data:\n{self.data}")
            return True

        logger.debug(f"ACCEPTED `{self.template}`")
        logger.debug(f"Data:\n{self.data}")
        return False
