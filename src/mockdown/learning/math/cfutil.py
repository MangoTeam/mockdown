from typing import List, NamedTuple, Union

import sympy as sym

ContinuedFraction = List[sym.Integer]


def cf_normalize(cf: ContinuedFraction) -> ContinuedFraction:
    """
    Normalizes a continued fraction representation.
    """
    if len(cf) <= 1:
        return cf

    if cf[-1] == 1:
        new_cf = cf[:-1]
        new_cf[-1] += 1
        return new_cf

    return cf


def cf_sb_parent(cf: ContinuedFraction) -> ContinuedFraction:
    assert cf == cf_normalize(cf)
    if cf == [sym.Number(1)]:
        return cf

    new_cf = cf[:-1] + [cf[-1] - 1]
    return cf_normalize(new_cf)


def cf_to_float(cf: ContinuedFraction) -> float:
    return float(sym.continued_fraction_reduce(cf))


def cf_to_rational(cf: ContinuedFraction) -> sym.Rational:
    return sym.continued_fraction_reduce(cf)


def cf_abs_err(cf: ContinuedFraction, n: float) -> float:
    return abs(cf_to_float(cf) - n)


def cf_rel_err(cf: ContinuedFraction, n: float) -> float:
    m = cf_to_float(cf)
    return abs(n - m) / max(abs(n), abs(m))
