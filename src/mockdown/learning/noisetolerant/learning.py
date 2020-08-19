import abc
import logging
import operator
from abc import abstractmethod
from fractions import Fraction
from math import floor, ceil
from typing import List, Sequence, Optional, Iterable, Tuple

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

                model = NoiseTolerantTemplateModel(template, data, self.config)

                if model.reject():
                    yield []
                else:
                    yield model.learn()

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


class NoiseTolerantTemplateModel(abc.ABC):
    def __init__(self, template: IConstraint, data: pd.DataFrame, config: NoiseTolerantLearningConfig):
        self.template = template
        self.data = data
        self.config = config

        x = sm.add_constant(self.x_data, has_constant='add')
        y = self.y_data
        kind = self.template.kind

        x_noise = np.random.randn(self.config.sample_count, 2) * 1e-5
        x = x.add(x_noise, axis=0)

        y_noise = np.random.randn(self.config.sample_count) * 1e-5
        y = y.add(y_noise, axis=0)

        self.model = sm.GLM(y, x)
        if kind.is_constant_form:
            self.fit = self.model.fit_constrained(((0, 1), 0))
        elif kind.is_mul_only_form:
            self.fit = self.model.fit_constrained(((1, 0), 0))
        elif kind.is_add_only_form:
            self.fit = self.model.fit_constrained(((0, 1), 1))
        else:
            self.fit = self.model.fit()

    @property
    def x_name(self) -> str:
        return str(self.template.x_id) if self.template.x_id else '__dummy__'

    @property
    def y_name(self) -> str:
        return str(self.template.y_id)

    @property
    def x_data(self) -> pd.Series:
        if self.template.kind.is_constant_form:
            return pd.Series(np.zeros(self.config.sample_count), name=self.x_name)
        return self.data[self.x_name]

    @property
    def y_data(self) -> pd.Series:
        return self.data[self.y_name]

    def learn(self) -> List[ConstraintCandidate]:
        return []

    def reject(self) -> bool:
        x, y = self.x_data, self.y_data

        if np.var(x) == 0 and not np.std(y) < self.config.cutoff_spread:
            logger.info(
                f"REJECTED `{self.template}`, no x variance and stdev of y is too high: "
                f"{np.std(y)} > {self.config.cutoff_spread}")
            logger.debug(f"Data:\n{self.data}")
            return True

        if np.var(y) == 0 and not np.std(x) < self.config.cutoff_spread:
            logger.info(
                f"REJECTED `{self.template}`, no y variance and stdev of x is too high: "
                f"{np.std(x)} > {self.config.cutoff_spread}")
            logger.debug(f"Data:\n{self.data}")
            return True

        # Are the residuals small?
        resid_std = np.std(self.fit.resid_response)
        if resid_std > self.config.cutoff_spread:
            logger.info(
                f"REJECTED `{self.template}`, stdev of residuals too high: {resid_std} > {self.config.cutoff_spread}")
            logger.debug(f"Data:\n{self.data}")
            return True

        self._log_accepted()
        return False

    def a_bounds(self) -> Tuple[Fraction, Fraction]:
        max_d = self.config.max_denominator
        al, au = self.fit.conf_int(alpha=self.config.a_alpha).iloc[1]
        return Fraction(al).limit_denominator(max_d), Fraction(au).limit_denominator(max_d)

    def b_bounds(self) -> Tuple[int, int]:
        bl, bu = self.fit.conf_int(alpha=self.config.b_alpha).iloc[0]
        return floor(bl), ceil(bu)

    def _log_accepted(self) -> None:
        a_bounds_str: str
        al, au = self.a_bounds()
        a_bounds_str = f"= {al}" if al == au else f"∈ [{al}, {au}]"

        bl, bu = self.b_bounds()
        b_bounds_str = f"= {bl}" if bl == bu else f"∈ [{bl}, {bu}]"

        logger.debug(f"ACCEPTED `{self.template}`")
        logger.debug(f"Bounds: a {a_bounds_str}, b {b_bounds_str}")
        logger.debug(f"Data:\n{self.data}")
