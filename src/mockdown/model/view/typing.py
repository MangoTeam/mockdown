from numbers import Number as PyNumber
from typing import Union, Callable

import sympy as sym

NumberConvertible = Union[str, int, float, sym.Number]
NumberFactory = Callable[[NumberConvertible], sym.Number]
