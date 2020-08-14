from __future__ import annotations

from fractions import Fraction
from math import floor, ceil
from typing import NoReturn, Tuple, TypeVar, Union

import sympy as sym

AnyNum = Union[int, float, Fraction]

_ElT = TypeVar('_ElT')
Tuple4 = Tuple[_ElT, _ElT, _ElT, _ElT]

# (NT = Numeric Type)
NT = TypeVar('NT', bound=sym.Number)


def to_int(x: NT) -> int:
    if isinstance(x, sym.Rational):
        num, denom = x.as_numer_denom()
        return round(num / denom)
    else:
        return int(x)


def to_frac(x: Union[sym.Rational, Fraction]) -> Fraction:
    if isinstance(x, Fraction):
        return x
    elif isinstance(x, sym.Rational):
        return Fraction(x.p, x.q)
    elif (isinstance(x, sym.Expr)):
        return Fraction(float(x.evalf()))
    else:
        unreachable(x)


def round_down(x: NT, places: int = 5) -> Fraction:
    return Fraction(floor(x * (10 ** places)), 10 ** places)


def round_up(x: NT, places: int = 5) -> Fraction:
    return Fraction(ceil(x * (10 ** places)), 10 ** places)


def round_frac(x: NT, places: int = 5) -> Fraction:
    return Fraction(round(x * (10 ** places)), 10 ** places)


def unreachable(x: NoReturn) -> NoReturn:
    """
    This is just like unreachable in any proof assistant.
    Usage:
    > class Foo(Enum):
    >     A = 1
    >     B = 2
    >     C = 3
    >thon
    > def foo_name(foo: Foo) -> str:
    >     if foo is Foo.A:
    >         return "apple"
    >     elif foo is Foo.B:
    >         return "banana":
    >     else:
    >         unreachable(foo)
    >

    Note: this only works with is! Not equality checks! (Unless it's a Literal type)

    Which outputs:

    > Argument 1 to "unreachable" has incompatible type "Literal[Foo.A]"; \
    >     expected "NoReturn"
    """
    assert False, "Unhandled type: {}".format(type(x).__name__)
