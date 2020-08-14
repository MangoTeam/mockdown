from functools import lru_cache
from math import ceil, floor, isclose
from typing import List, SupportsFloat, cast

from sympy import Integer, Rational, Number


@lru_cache
def farey(n: int = 100) -> List[Rational]:
    return [Rational(0, 1)] + sorted({
        Rational(m, k)
        for k in range(1, n + 1)
        for m in range(1, k + 1)
    })


@lru_cache
def ext_farey(n: int = 100) -> List[Rational]:
    """
    Farey sequence with its reversed reciprocals appended.
    Extends the sequence from 0-1 to 0-n.
    """
    # todo: fix the type error here by writing better stubs...

    f = farey(n)
    return f + [Rational(a.q, a.p) for a in reversed(f[1:-1])]


@lru_cache
def z_ball(center: Integer, diameter: float) -> List[Integer]:
    return [Integer(x) for x in range(
        ceil(center - diameter),
        floor(center + diameter)
    )]


@lru_cache
def q_ball(center: SupportsFloat,
           abs_tol: float = 0,
           rel_tol: float = 0.025,
           max_denominator: int = 100) -> List[Rational]:
    c = float(center)

    return list(filter(
        lambda q: isclose(c, float(q), abs_tol=abs_tol, rel_tol=rel_tol),
        ext_farey(n=max_denominator)
    ))


if __name__ == '__main__':
    print(farey())
