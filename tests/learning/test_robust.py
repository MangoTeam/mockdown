import sympy as sym
from hypothesis import given
from hypothesis.strategies import fractions, composite

from mockdown.learning.util import cf_normalize, cf_sb_parent


@composite
def rationals(draw, *args, **kwargs):
    fraction = draw(fractions(*args, **kwargs))
    return sym.Rational(fraction.numerator, fraction.denominator)


@composite
def continued_fractions(draw, *args, **kwargs):
    rational = draw(rationals(*args, **kwargs))
    return sym.continued_fraction(rational)


@given(continued_fractions())
def test_cf_normalize_works(cf):
    cf_normalize(cf)


def test_cf_normalize_examples():
    f1 = sym.Rational(23, 16)
    cf1 = sym.continued_fraction(f1)
    assert cf1 == [1, 2, 3, 2]
    assert cf_normalize([1, 2, 3, 1, 1]) == cf1


@given(continued_fractions())
def test_cf_sb_parent_works(cf):
    cf_sb_parent(cf)


def test_cf_sb_parent_examples():
    f1 = sym.Rational(13, 20)
    cf1 = sym.continued_fraction(f1)
    cf2 = cf_sb_parent(cf1)
    cf3 = cf_sb_parent(cf2)
    cf4 = cf_sb_parent(cf3)
    cf5 = cf_sb_parent(cf4)
    cf6 = cf_sb_parent(cf5)
    cf7 = cf_sb_parent(cf6)
    cf8 = cf_sb_parent(cf7)
    cf9 = cf_sb_parent(cf8)
    cf10 = cf_sb_parent(cf9)

    assert sym.continued_fraction_reduce(cf2) == sym.Rational(11, 17)
    assert sym.continued_fraction_reduce(cf3) == sym.Rational(9, 14)
    assert sym.continued_fraction_reduce(cf4) == sym.Rational(7, 11)
    assert sym.continued_fraction_reduce(cf5) == sym.Rational(5, 8)
    assert sym.continued_fraction_reduce(cf6) == sym.Rational(3, 5)
    assert sym.continued_fraction_reduce(cf7) == sym.Rational(2, 3)
    assert sym.continued_fraction_reduce(cf8) == sym.Rational(1, 2)
    assert sym.continued_fraction_reduce(cf9) == sym.Rational(1)

    # Idempotency at top of tree.
    assert sym.continued_fraction_reduce(cf10) == sym.Rational(1)

