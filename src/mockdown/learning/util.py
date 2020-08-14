import operator
from typing import Any

import sympy as sym
from sympy import Rational, continued_fraction

from mockdown.constraint.types import IComparisonOp


def widen_bound(op: IComparisonOp[Any], old: sym.Number, new: sym.Number) -> sym.Number:
    if op == operator.le:
        mx = sym.Max(old, new)  # type: ignore
        assert isinstance(mx, sym.Number)
        return mx
    elif op == operator.ge:
        mn = sym.Min(old, new)  # type: ignore
        assert isinstance(mn, sym.Number)
        return mn
    else:
        raise Exception("unsupported operator")


def sb_depth(q: Rational) -> int:
    """
    Note: this sum is equal to the depth in the Stern-Brocot tree.

    The "irrationality" is more properly defined as length, but this works better.
    """
    return int(sum(continued_fraction(q)))