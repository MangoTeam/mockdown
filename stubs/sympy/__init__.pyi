from __future__ import annotations

from fractions import Fraction
from typing import TypeVar, Union, SupportsAbs, SupportsFloat, Tuple, SupportsRound, SupportsInt, overload, List

from .ntheory import continued_fraction

# noinspection PyUnresolvedReferences
__all__ = [
    'Basic',
    'Atom',
    'Number',
    'Float',
    'Rational',
    'Integer',
    'continued_fraction',
    'continued_fraction_reduce'
]

"""
Some type stubs to make mypy happy when dealing with sympy.
Warning: these may have subtle problems, after all, we wrote them...
"""

N = TypeVar('N', bound='Number')
# N_co = TypeVar('N_co', bound='Number', covariant=True)
# N_contra = TypeVar('N_contra', bound='Number', contravariant=True)

# Type of anything that is compatible with Number's operators.
_AnyNum = Union['Number', int, float]
_AnyNum_contra = TypeVar('_AnyNum_contra', bound=_AnyNum, contravariant=True)

# Type of things convertible to a Number.
_ToNum = Union['Number', str, int, float, Fraction]


class Basic: ...


class Atom(Basic): ...


class Expr(Basic): ...


class AtomicExpr(Atom, Expr): ...


class Number(AtomicExpr, SupportsAbs['Number'], SupportsInt, SupportsFloat, SupportsRound[int]):
    def __init__(self, value: _ToNum) -> None: ...

    def __add__(self: N, other: _AnyNum) -> N: ...

    def __sub__(self: N, other: _AnyNum) -> N: ...

    def __truediv__(self: N, other: _AnyNum) -> N: ...

    def __abs__(self: N) -> N: ...

    def __round__(self, ndigits: int = 0) -> int: ...

    def __int__(self: N) -> int: ...

    def __float__(self: N) -> float: ...

    def __lt__(self: N, other: _AnyNum) -> bool: ...

    def __le__(self: N, other: _AnyNum) -> bool: ...

    def __gt__(self: N, other: _AnyNum) -> bool: ...

    def __ge__(self: N, other: _AnyNum) -> bool: ...

    def __eq__(self: N, other: object) -> bool: ...


class Float(Number): ...


class Rational(Number):
    @overload
    def __init__(self, x: int): ...

    @overload
    def __init__(self, x: Number): ...

    @overload
    def __init__(self, p: int, q: int): ...

    @overload
    def __init__(self, p: Integer, q: Integer): ...

    @overload
    def __truediv__(self, other: int) -> Rational: ...

    @overload
    def __truediv__(self, other: Rational) -> Rational: ...

    @overload
    def __rtruediv__(self, other: int) -> Rational: ...

    @overload
    def __rtruediv__(self, other: Rational) -> Rational: ...

    @property
    def p(self) -> Integer: ...

    @property
    def q(self) -> Integer: ...

    def limit_denominator(self, max_denominator: int) -> Rational: ...

    def as_numer_denom(self) -> Tuple[Integer, Integer]: ...



class Integer(Rational): ...

def continued_fraction_reduce(cf: List[N]) -> Union[Rational, Float]: ...