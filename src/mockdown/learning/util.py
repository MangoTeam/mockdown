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


class CandidateRational(NamedTuple):
    value: sym.Rational
    depth: int
    abs_err: float
    rel_err: float


def candidate_rationals(n: Union[sym.Float, float],
                        max_denominator: int = 100,
                        abs_eps: float = 0.5,
                        rel_eps: float = 0.05) -> List[CandidateRational]:
    q = n if isinstance(n, sym.Rational) else sym.Rational(n)
    q = q.limit_denominator(max_denominator)
    cf = sym.continued_fraction(q)
    n = float(n)

    results = []
    while cf != [1]:
        abs_err = cf_abs_err(cf, n)
        rel_err = cf_rel_err(cf, n)
        depth = sum(cf)
        result = CandidateRational(cf_to_rational(cf), depth, abs_err, rel_err)
        cf = cf_sb_parent(cf)

        if abs_err < abs_eps and rel_err < rel_eps:
            results.append(result)

    return results