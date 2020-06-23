from typing import Any, Callable, Sequence

from sympy import Number

from mockdown.constraint import ConstraintKind, IConstraint
from mockdown.learning.typing import IConstraintLearning
from mockdown.model import IView
from mockdown.typing import NT

Kind = ConstraintKind

DEFAULT_TOLERANCE = 0.01  # maximum difference of 1%
MAX_DENOMINATOR = 1000

PriorCallable = Callable[[NT], Any]


class RobustLearning(IConstraintLearning):
    """
    This class emulates the old learning method.

    The one difference is that it rationalizes its output.
    """

    def __init__(self,
                 templates: Sequence[IConstraint],
                 samples: Sequence[IView[Number]],
                 confidence_threshold: int = 0.95):
        """
        :param confidence_threshold: cutoff for returned constraints, 0-1.
        """
        self._templates = templates
        self._samples = samples
        self._confidence_threshold = confidence_threshold

    def learn(self) -> Sequence[IConstraint]:
        pass
