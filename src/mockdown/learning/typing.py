from abc import abstractmethod
from typing import Protocol, Sequence

from mockdown.constraint import IConstraint


class IConstraintLearning(Protocol):
    @abstractmethod
    def learn(self) -> Sequence[IConstraint]: ...
