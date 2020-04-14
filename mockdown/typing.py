from fractions import Fraction
# from numbers import Real, Rational, Integral
from typing import TypeVar, NoReturn

# This is used everywhere, so we define them once here.
# Note, the protocols from Numbers proved weird.
NT = TypeVar('NT', int, float, Fraction)
NT_Co = TypeVar('NT_Co', int, float, Fraction, covariant=True)
NT_Contra = TypeVar('NT_Contra', int, float, Fraction, contravariant=True)


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
