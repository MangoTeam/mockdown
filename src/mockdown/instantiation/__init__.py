import os

from .numpy import NumpyConstraintInstantiator
from .types import IConstraintInstantiator


def get_prolog_instantiator_factory():
    if os.name != 'nt':
        from .prolog import PrologConstraintInstantiator
        return PrologConstraintInstantiator
    else:
        return lambda _: NotImplemented


__all__ = [
    'IConstraintInstantiator',
    'NumpyConstraintInstantiator',
    'get_prolog_instantiator_factory'
]
