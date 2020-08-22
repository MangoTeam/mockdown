import abc
import logging
import operator
from fractions import Fraction
from math import floor, ceil
from typing import List, Sequence, Optional, Iterable, Tuple

import numpy as np  # type: ignore
import pandas as pd  # type: ignore
import statsmodels.api as sm  # type: ignore
import sympy as sym

from mockdown.constraint import IConstraint
from mockdown.learning.noisetolerant.types import NoiseTolerantLearningConfig
from mockdown.learning.types import IConstraintLearning, ConstraintCandidate
from mockdown.model import IView
from mockdown.types import unopt

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
                yield model.learn() if not model.reject() else []

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

    def likelihood_score(self, a: int, b: Fraction, scale=1) -> float:
        return self.model.loglike((b, a), scale=scale)

    def candidates(self) -> pd.DataFrame:
        a_space, b_space = self.config.a_space, self.config.b_space
        aconf_l, aconf_u = self.a_confint()
        bconf_l, bconf_u = self.b_confint()

        a_cands_ixs = np.where(np.logical_and(aconf_l <= a_space, a_space <= aconf_u))[0]
        if len(a_cands_ixs) == 0:
            # The confidence interval is _between_ two candidates, find its upper/lower candidate bounds.
            a_ix = np.searchsorted(a_space, (aconf_l + aconf_u) / 2)
            a_cands_ixs = [max(0, a_ix - 1), a_ix]
        a_cands = a_space[a_cands_ixs]

        b_cands_ixs = np.where(np.logical_and(bconf_l <= b_space, b_space <= bconf_u))[0]
        if len(b_cands_ixs) == 0:
            # The confidence interval is _between_ two candidates, find its upper/lower candidate bounds.
            b_ix = np.searchsorted(b_space, (bconf_l + bconf_u) / 2)
            b_cands_ixs = [max(0, b_ix - 1), b_ix]
        b_cands = b_space[b_cands_ixs]

        return pd.DataFrame([(a, b) for a in a_cands for b in b_cands], columns=['a', 'b'])

    def learn(self) -> List[ConstraintCandidate]:
        candidates = self.candidates()
        # scale = 1

        candidates['glm_loglike'] = candidates.apply(lambda c: self.likelihood_score(*c), axis=1)
        candidates['glm_score'] = np.exp(candidates['glm_loglike'])
        candidates['glm_score'] /= candidates['glm_score'].sum()

        candidates['pri_score'] = self.a_prior(candidates['a'])
        candidates['pri_score'] /= candidates['pri_score'].sum()

        candidates['score'] = candidates['glm_score'] * candidates['pri_score']
        candidates['log_score'] = np.log(candidates['score'])

        logger.info(f"CANDIDATES:\n{candidates}")

        return list(candidates.apply(lambda row: ConstraintCandidate(
            self.template.subst(a=sym.Rational(row['a']), b=sym.Rational(row['b'])),
            row['score']), axis=1))

    def reject(self) -> bool:
        x, y = self.x_data, self.y_data

        if np.var(x) == 0 and not np.std(y) < self.config.cutoff_spread:
            logger.info(
                f"REJECTED: `{self.template}`, no x variance and stdev of y is too high: "
                f"{np.std(y)} > {self.config.cutoff_spread}")
            logger.debug(f"Data:\n{self.data}")
            return True

        if np.var(y) == 0 and not np.std(x) < self.config.cutoff_spread:
            logger.info(
                f"REJECTED: `{self.template}`, no y variance and stdev of x is too high: "
                f"{np.std(x)} > {self.config.cutoff_spread}")
            logger.debug(f"Data:\n{self.data}")
            return True

        # Are the residuals small?
        resid_std = np.std(self.fit.resid_response)
        if resid_std > self.config.cutoff_spread:
            logger.info(
                f"REJECTED: `{self.template}`, stdev of residuals too high: {resid_std} > {self.config.cutoff_spread}")
            logger.debug(f"Data:\n{self.data}")
            return True

        self._log_accepted()
        return False

    def a_confint(self) -> Tuple[float, float]:
        max_d = self.config.max_denominator
        al, au = self.fit.conf_int(alpha=self.config.a_alpha).iloc[1]
        return al, au

    def b_confint(self) -> Tuple[float, float]:
        bl, bu = self.fit.conf_int(alpha=self.config.b_alpha).iloc[0]
        return bl, bu

    def a_prior(self, a: np.ndarray) -> float:
        return self.config.depth_prior[np.searchsorted(self.config.a_space, a)]

    def _log_accepted(self) -> None:
        a_bounds_str: str
        al, au = self.a_confint()
        a_bounds_str = f"= {al}" if al == au else f"∈ [{al}, {au}]"

        bl, bu = self.b_confint()
        b_bounds_str = f"= {bl}" if bl == bu else f"∈ [{bl}, {bu}]"

        logger.info(f"ACCEPTED: `{self.template}`")
        logger.debug(f"DATA:\n{self.data}")
        logger.info(f"BOUNDS: a {a_bounds_str}, b {b_bounds_str}")
