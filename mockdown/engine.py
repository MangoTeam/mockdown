from abc import abstractmethod
from typing import Protocol, Sequence, Set

from .model import IView
from .constraint import IConstraint
from .instantiation import IConstraintInstantiator, VisibilityConstraintInstantiator
from .typing import NT, NT_co


class IMockdownEngine(Protocol[NT_co]):
    @property
    @abstractmethod
    def instantiation_engine(self) -> IConstraintInstantiator: ...

    @property
    @abstractmethod
    def training_behavior(self) -> None: ...

    @property
    @abstractmethod
    def selection_behavior(self) -> None: ...

    def run(self, examples: Sequence[IView[NT]]) -> Set[IConstraint]:
        templates = self.instantiation_engine.instantiate(examples)
        # todo: train and prune
        return templates


class OldMockdownEngine(IMockdownEngine):
    def __init__(self):
        self._instantiation_engine = VisibilityConstraintInstantiator()

    @property
    def instantiation_engine(self) -> IConstraintInstantiator:
        return self._instantiation_engine

    @property
    def training_behavior(self) -> None:
        return None

    @property
    def selection_behavior(self) -> None:
        return None


class RobustMockdownEngine:
    pass
