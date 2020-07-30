from __future__ import annotations

from typing import NoReturn, Tuple, TypeVar

import sympy as sym

_ElT = TypeVar('_ElT')
Tuple4 = Tuple[_ElT, _ElT, _ElT, _ElT]

# (NT = Numeric Type)
NT = TypeVar('NT', bound=sym.Number)


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
