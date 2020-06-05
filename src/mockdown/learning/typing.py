from abc import abstractmethod
from dataclasses import dataclass
from typing import Protocol, Sequence, List

from mockdown.constraint import IConstraint


@dataclass
class ConstraintCandidate:
    constraint: IConstraint
    score: float


class IConstraintLearning(Protocol):
    @abstractmethod
    def learn(self) -> List[List[ConstraintCandidate]]: ...
