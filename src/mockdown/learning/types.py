from abc import abstractmethod
from dataclasses import dataclass
from typing import Protocol, List, Sequence, Any, Dict

import sympy as sym

from mockdown.constraint import IConstraint
from mockdown.model import IView


@dataclass
class ConstraintCandidate:
    constraint: IConstraint
    score: float


class IConstraintLearning(Protocol):
    @abstractmethod
    def __init__(self,
                 templates: Sequence[IConstraint],
                 samples: Sequence[IView[sym.Number]],
                 *args: List[Any],
                 **kwargs: Dict[str, Any]) -> None: ...

    @abstractmethod
    def learn(self) -> List[List[ConstraintCandidate]]: ...
