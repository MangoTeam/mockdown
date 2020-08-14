from typing import List, Sequence

import sympy as sym

from mockdown.constraint import IConstraint
from mockdown.learning.bayesian.types import BayesianLearningConfig
from mockdown.learning.types import IConstraintLearning, ConstraintCandidate
from mockdown.model import IView


class BayesianLearning(IConstraintLearning):
    def __init__(self,
                 templates: Sequence[IConstraint],
                 samples: Sequence[IView[sym.Number]],
                 config: BayesianLearningConfig):
        raise NotImplementedError()

    def learn(self) -> List[List[ConstraintCandidate]]:
        raise NotImplementedError()

