import logging
import operator
from abc import abstractmethod
from typing import List, Sequence, Any, Dict, Optional

import sympy as sym
import statsmodels.api as sm
import pandas as pd
import numpy as np
import scipy.stats as st

from mockdown.constraint import IConstraint
from mockdown.learning.fancy.types import FancyLearningConfig
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
        def gen_cands():
            for template in self.templates:
                data = self.find_template_data(template)
                if template.kind.is_constant_form:
                    task = FancyConstantTemplateLearning(template, data, self.config)
                else:
                    task = FancyLinearTemplateLearning(template, data, self.config)

                if task.reject():
                    yield []
                else:
                    yield task.learn()

        return list(gen_cands())

    def find_template_data(self, template: IConstraint):
        """Extract the data for a given template from the samples."""
        if template.kind.is_constant_form:
            columns = [template.y_id]
        else:
            columns = [template.y_id, template.x_id]

        rows = []
        for sample in self.samples:
            rows.append([sample.find_anchor(col).value for col in columns])

        return pd.DataFrame(rows, columns=list(map(str, columns)), dtype=np.float)


class FancyTemplateLearning:
    def __init__(self, template: IConstraint, data: pd.DataFrame, config: FancyLearningConfig):
        self.template = template
        self.data = data
        self.config = config

    @property
    def x_name(self):
        return str(self.template.x_id)

    @property
    def y_name(self):
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

        # Is the sample variance small enough?
        rsd = (np.std(y_data) / np.mean(y_data)).item()
        if rsd > self.config.cutoff_rsd:
            logger.info(f"Rejecting template {self.template}, RSD too high: {rsd} > {self.config.cutoff_rsd}")
            logger.debug(f"Data:\n{self.data}")
            return True

        # Note: Shapiro-Wilk doesn't work when stdev (or rsd) = 0.
        if rsd == 0:
            return False

        # Do the residuals appear to be normal?
        _, p = st.shapiro(y_data - np.mean(y_data))
        if p < self.config.cutoff_fit:
            logger.info(f"Rejecting template {self.template}, failed normality test.")
            logger.debug(f"Data:\n{self.data}")
            return True

        return False


class FancyLinearTemplateLearning(FancyTemplateLearning):
    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)

        # THIS IS A HORRIBLE HACK:
        # Basically, linregress gets mad when there are covariance terms that are identically 0.
        # So we actually _add_ noise to the data (but the teeeeeeeeeeeeeeeeensiest possible bit)
        hack_noise = st.norm.rvs(scale=20 * np.finfo(np.float).eps, size=self.data.size).reshape(self.data.shape)
        hack_data = self.data + hack_noise

        self.mle_a, self.mle_b, self.mle_r, self.mle_p, _ = st.linregress(hack_data[self.x_name],
                                                                          hack_data[self.y_name])

    def learn(self) -> List[ConstraintCandidate]:
        return []

    def reject(self) -> bool:
        # Do we fail to reject the null-hypothesis that the slope is 0?
        if not self.mle_p < self.config.cutoff_fit:
            logger.info(f"Rejecting template {self.template}, failed linear-regression Wald test "
                        f"(p = {self.mle_p} ≥ {self.config.cutoff_fit})")
            logger.debug(f"Data:\n{self.data}")

        # Are the residuals small?


        # Does the data's slope appear negative?
        if self.mle_r < 0:
            logger.info(f"Rejecting template {self.template}, slope is negative.")
            logger.debug(f"Data:\n{self.data}")
        return False
