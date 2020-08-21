from typing import Sequence

from mockdown.constraint import IConstraint
from mockdown.instantiation.types import IConstraintInstantiator
from mockdown.model import IView
from mockdown.types import NT


class NumpyConstraintInstantiator(IConstraintInstantiator[NT]):
    def __init__(self, examples: Sequence[IView[NT]]):
        self.examples = examples

    def instantiate(self) -> Sequence[IConstraint]:
        raise NotImplementedError()
