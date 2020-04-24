from abc import abstractmethod
from typing import Protocol, Sequence, Set

from .model import IView
from .constraint import IConstraint
from .instantiation import IConstraintInstantiator, VisibilityConstraintInstantiator
from .typing import NT, NT_co


class IMockdownEngine(Protocol[NT]):
    @property
    @abstractmethod
    def instantiation_engine(self) -> IConstraintInstantiator[NT]: ...

    @property
    @abstractmethod
    def training_behavior(self) -> None: ...

    @property
    @abstractmethod
    def selection_behavior(self) -> None: ...

    def run(self, examples: Sequence[IView[NT]]) -> Sequence[IConstraint]:
        templates = self.instantiation_engine.instantiate(examples)
        # todo: train and prune
        return templates


class DefaultMockdownEngine(IMockdownEngine[float]):
    def __init__(self) -> None:
        self._instantiation_engine = VisibilityConstraintInstantiator()

    @property
    def instantiation_engine(self) -> IConstraintInstantiator[float]:
        return self._instantiation_engine

    @property
    def training_behavior(self) -> None:
        return None

    @property
    def selection_behavior(self) -> None:
        return None


class RobustMockdownEngine:
    pass