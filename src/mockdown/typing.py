from fractions import Fraction
from typing import NoReturn, Tuple, TypeVar, Union

from math import floor, ceil

AnyNum = Union[int, float, Fraction]

_T = TypeVar('_T')
Tuple4 = Tuple[_T, _T, _T, _T]

NT = TypeVar('NT', int, float, Fraction)
NT_co = TypeVar('NT_co', int, float, Fraction, covariant=True)
NT_contra = TypeVar('NT_contra', int, float, Fraction, contravariant=True)

def to_int(x: NT) -> int:
    if (isinstance(x, Fraction)):
        num,denom = x.as_integer_ratio()
        return round(num/denom)
    else: 
        return int(x)

def to_frac(x: NT) -> Fraction:
    if (isinstance(x, Fraction)):
        return x
    else: 
        return Fraction(x)


def round_down(x: NT, places: int = 5) -> Fraction:
    return Fraction(floor(x * (10 ** places)), 10 ** places)

def round_up(x: NT, places: int = 5) -> Fraction:
    return Fraction(ceil(x * (10 ** places)), 10 ** places)

def round_frac(x: NT, places: int = 5) -> Fraction:
    return Fraction(round(x * (10 ** places)), 10 ** places)

# (NT = Numeric Type)

def unreachable(x: NoReturn) -> NoReturn:
    """
    This is just like unreachable in any proof assistant.
    Usage:
    > class Foo(Enum):
    >     A = 1
    >     B = 2
    >     C = 3
    >
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
