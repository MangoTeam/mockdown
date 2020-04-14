from abc import abstractmethod
from typing import Protocol, Collection, Sequence

from ..constraint import IConstraint
from ..model import IView
from ..typing import NT


class IConstraintInstantiator(Protocol[NT]):
    """
    An "instantiation engine" handles generating a set of constraint templates
    for the provided examples.
    """

    @abstractmethod
    def instantiate(self, examples: Sequence[IView[NT]]) -> Collection[IConstraint]:
        """
        Given a set of examples, instantiate a set of constraints to train.
        """
        ...
