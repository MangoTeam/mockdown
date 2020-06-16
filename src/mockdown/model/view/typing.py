from numbers import Number as PyNumber
from typing import Union, Callable

from sympy import Number

NumberConvertible = Union[str, PyNumber, Number]
NumberFactory = Callable[[NumberConvertible], Number]