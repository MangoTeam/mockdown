from fractions import Fraction
from math import floor, ceil
from typing import Union, SupportsFloat, Literal

import sympy as sym

from mockdown.constraint import IConstraint
from mockdown.types import NT, unreachable

from mockdown.model import View, IAnchorID

# def local_anchors(v: View) -> Iterable[IAnchorID]:
#     for box in [v, *v.children]:
#         for anchor in box.anchors:
#             yield anchor

def anchor_equiv(c1: IConstraint, c2: IConstraint) -> bool:
    """
    Equivalence modulo anchors.
    """
    return c1.y_id == c2.y_id and c1.x_id == c2.x_id


def short_str(cn: IConstraint) -> str:
    import operator
    op_str = {
        operator.eq: '=',
        operator.le: '≤',
        operator.ge: '≥'
    }[cn.op]

    if cn.x_id:
        a_str = "" if cn.a == 1.0 else f"{cn.a} * "
        b_str = "" if cn.b == 0 else f" {'+' if cn.b >= 0 else '-'} {abs(cn.b)}"
        return f"{str(cn.y_id)} {op_str} {a_str}{str(cn.x_id)}{b_str}"
    else:
        return f"{str(cn.y_id)} {op_str} {str(cn.b)}"


def to_int(x: SupportsFloat, rounding: Literal['up', 'down', 'nearest'] = 'down') -> int:
    if rounding == 'up':
        return ceil(float(x))
    elif rounding == 'down':
        return floor(float(x))
    elif rounding == 'nearest':
        return round(float(x))
    else:
        unreachable(x)


def to_frac(x: Union[NT, Fraction]) -> Fraction:
    if isinstance(x, Fraction):
        return x
    elif isinstance(x, sym.Rational):
        return Fraction(int(x.p), int(x.q))
    elif isinstance(x, sym.Expr):
        return Fraction(float(x.evalf()))
    else:
        unreachable(x)


def round_down(x: NT, places: int = 5) -> Fraction:
    return Fraction(floor(x * (10 ** places)), 10 ** places)


def round_up(x: NT, places: int = 5) -> Fraction:
    return Fraction(ceil(x * (10 ** places)), 10 ** places)


def round_frac(x: NT, places: int = 5) -> Fraction:
    return Fraction(round(x * (10 ** places)), 10 ** places)