from fractions import Fraction
# from numbers import Real, Rational, Integral
from typing import TypeVar

# This is used everywhere, so we define them once here.
# Note, the protocols from Numbers proved weird.
NT = TypeVar('NT', int, float, Fraction)
NT_Co = TypeVar('NT_Co', int, float, Fraction, covariant=True)
NT_Contra = TypeVar('NT_Contra', int, float, Fraction, contravariant=True)

# (NT = Numeric Type)
