from fractions import Fraction
# from numbers import Real, Rational, Integral
from typing import NoReturn, TypeVar, Union

AnyNum = Union[int, float, Fraction]

_T = TypeVar('_T')
Tuple4 = Tuple[_T, _T, _T, _T]

NT = TypeVar('NT', int, float, Fraction)
NT_co = TypeVar('NT_co', int, float, Fraction, covariant=True)
NT_contra = TypeVar('NT_contra', int, float, Fraction, contravariant=True)


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

    Note: this only works with is! Not equality checks!

    Which outputs:

    > Argument 1 to "unreachable" has incompatible type "Literal[Foo.A]"; \
    >     expected "NoReturn"
    """
    assert False, "Unhandled type: {}".format(type(x).__name__)
