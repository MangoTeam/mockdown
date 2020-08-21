from typing import Sequence

from mockdown.constraint import IConstraint
from mockdown.instantiation import IConstraintInstantiator
from mockdown.model import IView
from mockdown.types import NT


class NumpyConstraintInstantiator(IConstraintInstantiator):
    def instantiate(self, examples: Sequence[IView[NT]]) -> Sequence[IConstraint]:
        raise NotImplementedError()
