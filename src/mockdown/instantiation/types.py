from abc import abstractmethod
from typing import Protocol, Collection, Sequence, Set

from mockdown.constraint import IConstraint
from mockdown.model import IView
from mockdown.types import NT


class IConstraintInstantiator(Protocol[NT]):
    """
    An "instantiation engine" handles generating a set of constraint templates
    for the provided examples.
    """

    @abstractmethod
    def instantiate(self, examples: Sequence[IView[NT]]) -> Sequence[IConstraint]:
        """
        Given a set of examples, instantiate a set of constraints to train.
        """
        ...
