import os

from .numpy import NumpyConstraintInstantiator
from .types import IConstraintInstantiator

if os.name != 'nt':
    from .prolog import PrologConstraintInstantiator
    __all__ = [
        'IConstraintInstantiator',
        'PrologConstraintInstantiator',
        'NumpyConstraintInstantiator'
    ]
else:
    __all__ = [
        'IConstraintInstantiator',
        'NumpyConstraintInstantiator'
    ]

