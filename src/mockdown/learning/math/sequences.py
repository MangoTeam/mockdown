from functools import lru_cache
from math import ceil, floor
from typing import List

from sympy import Integer, Rational


@lru_cache
def farey(n=100) -> List[Rational]:
    return [Rational(0, 1)] + sorted({
        Rational(m, k)
        for k in range(1, n + 1)
        for m in range(1, k + 1)
    })


@lru_cache
def z_ball(center: Integer, diameter: float) -> List[Integer]:
    return [Integer(x) for x in range(
        ceil(center - diameter),
        floor(center + diameter)
    )]


@lru_cache
def q_ball(center: Rational, diameter: float, max_denominator=100) -> List[Rational]:
    return list(filter(
        lambda q: center - diameter <= q <= center + diameter,
        farey(n=max_denominator)
    ))


if __name__ == '__main__':
    print(farey())
