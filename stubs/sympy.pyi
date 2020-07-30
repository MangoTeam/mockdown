from __future__ import annotations
from typing import TypeVar, Any, overload, Union, SupportsAbs, _T_co, SupportsFloat

from fractions import Fraction

"""
Some type stubs to make mypy happy when dealing with sympy.
Warning: these may have subtle problems, after all, we wrote them...
"""

N = TypeVar('N', bound='Number')

# Type of anything that is compatible with Number's operators.
_AnyNum = Union['Number', int, float]

# Type of things convertible to a Number.
_ToNum = Union['Number', str, int, float, Fraction]


class Basic: ...


class Atom(Basic): ...


class Expr(Basic): ...


class AtomicExpr(Atom, Expr): ...


class Number(AtomicExpr, SupportsAbs['Number'], SupportsFloat):
    def __init__(self, value: _ToNum) -> None: ...

    def __add__(self: N, other: _AnyNum) -> N: ...

    def __sub__(self: N, other: _AnyNum) -> N: ...

    # todo: this is incorrect for int/int -> rat
    def __truediv__(self: N, other: _AnyNum) -> N: ...

    def __abs__(self: N) -> N: ...

    def __float__(self: N) -> float: ...

    def __lt__(self: N, other: _AnyNum) -> bool: ...

    def __le__(self: N, other: _AnyNum) -> bool: ...

    def __gt__(self: N, other: _AnyNum) -> bool: ...

    def __ge__(self: N, other: _AnyNum) -> bool: ...

    def __eq__(self: N, other: object) -> bool: ...


class Float(Number): ...


class Rational(Number):
    def limit_denominator(self, max_denominator: int) -> Rational: ...


class Integer(Rational): ...

