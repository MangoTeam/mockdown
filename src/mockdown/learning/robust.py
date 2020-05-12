from typing import Any, Callable, Dict, Generic, Sequence

from mockdown.constraint import ConstraintKind, IConstraint
from mockdown.learning.typing import IConstraintLearning
from mockdown.model import IView
from mockdown.typing import NT

Kind = ConstraintKind

DEFAULT_TOLERANCE = 0.01  # maximum difference of 1%
MAX_DENOMINATOR = 1000

PriorCallable = Callable[[NT], Any]


class Priors(Generic[NT]):
    @staticmethod
    def get_by_kind(constraint_kind: ConstraintKind) -> Dict[ConstraintKind, PriorCallable[NT]]:
        return {
            ConstraintKind.POS_LTRB_OFFSET: Priors.lrtb_offset_prior
        }

    @staticmethod
    def lrtb_offset_prior(b: NT) -> Any:
        pass


class SimpleConstraintLearning(IConstraintLearning):
    """
    This class emulates the old learning method.

    The one difference is that it rationalizes its output.
    """

    def __init__(self,
                 templates: Sequence[IConstraint],
                 samples: Sequence[IView[float]]):
        self._templates = templates
        self._samples = samples

    def learn(self) -> Sequence[IConstraint]:
        pass
