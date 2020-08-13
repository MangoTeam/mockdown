from dataclasses import dataclass
from fractions import Fraction
from typing import List, Tuple, Any

import sympy as sym
from z3 import z3  # type: ignore

from mockdown.integration import anchor_id_to_z3_var
from mockdown.model import IAnchor, IView
from mockdown.model.primitives import Rect
from mockdown.types import NT, to_frac, round_frac, round_up, round_down
from .types import ISizeBounds


@dataclass(frozen=True)
class Conformance:
    width: Fraction
    height: Fraction
    x: Fraction
    y: Fraction

    def __lt__(self, other: Any) -> bool:
        if type(other) is Conformance:
            r: Conformance = other
            return self.width < r.width and self.height < r.height \
                and self.x < r.x and self.y < r.y
        else:
            raise Exception("what")

def from_rect(rect: Rect[NT]) -> Conformance:
    return Conformance(to_frac(rect.width), to_frac(rect.height), to_frac(rect.left), to_frac(rect.top))

def to_rect(conf: Conformance) -> Rect[sym.Rational]:
    return Rect(sym.Rational(conf.x), sym.Rational(conf.y), sym.Rational(conf.x + conf.width), sym.Rational(conf.y + conf.height))

def confs_to_bounds(lo_c: Conformance, hi_c: Conformance) -> ISizeBounds:
    return ISizeBounds({'min_w': lo_c.width, 'min_h': lo_c.height, 'max_w': hi_c.width, 'max_h': hi_c.height})

# def view_to_conf(view: IView[NT]) -> Conformance:


def conformance_range(lower: Conformance, upper: Conformance, scale: int = 10) -> List[Conformance]:

    # if not (lower < upper or lower == upper):
    #     if (lower > upper):
    #         tmp = lower
    #         lower = upper
    #         upper = lower
    #     else:
    #         raise Exception("incomparable arguments to range: [%s, %s]" % (lower, upper))
    
    # create several evenly spaced conformances on the range [min conf...max conf]
    # print(upper, lower)
    diff_h = Fraction(upper.height - lower.height, scale)
    diff_w = Fraction(upper.width - lower.width, scale)
    diff_x = Fraction(upper.x - lower.x, scale)
    diff_y = Fraction(upper.y - lower.y, scale)

    # def scaler(start: int, diff: int) -> int:

    # print('diffs: ', diff_h, diff_w)
    if diff_h == 0 and diff_w == 0 and diff_x == 0 and diff_y == 0:
        # print('optimizing!')
        return [lower]

    def builder(step: int) -> Conformance:
        return Conformance(lower.width + diff_w * step, lower.height + diff_h * step, lower.x + diff_x * step, lower.y + diff_y * step)
    
    # print('min/max:', self.max_conf, self.max_conf.width)

    # ensure the range is stable by manually adding the upper and lower bounds

    return [lower] + [builder(step) for step in range(1, scale-1)] + [upper]

def conservative_round(low: Tuple[NT, NT, NT, NT], high: Tuple[NT, NT, NT, NT]) -> Tuple[Conformance, Conformance]:
    lows, highs = list(low), list(high)
    output = []

    for idx in range(len(lows)):
        lo, hi = lows[idx], highs[idx]

        if hi > lo:
            output.append((round_up(lo), round_down(hi)))
        elif hi == lo:
            output.append((round_frac(lo), round_frac(lo)))
        else:
            output.append((round_down(lo), round_up(hi)))


    lo_c: Conformance = Conformance(*[x for x,_ in output])
    hi_c: Conformance = Conformance(*[y for _,y in output])

    return (lo_c, hi_c)

def add_conf_dims(solver: z3.Optimize, conf: Conformance, confIdx: int, targets: Tuple[IAnchor[NT],IAnchor[NT],IAnchor[NT],IAnchor[NT]]) -> None:
        top_x, top_y, top_width, top_height = targets
        
        top_x_v = anchor_id_to_z3_var(top_x.id, confIdx)
        top_y_v = anchor_id_to_z3_var(top_y.id, confIdx)
        top_w_v = anchor_id_to_z3_var(top_width.id, confIdx)
        top_h_v = anchor_id_to_z3_var(top_height.id, confIdx)

        solver.add(top_w_v == conf.width)
        solver.add(top_h_v == conf.height)
        solver.add(top_x_v == conf.x)
        solver.add(top_y_v == conf.y)

def conf_zip(conf: Conformance, view: IView[NT]) -> List[Tuple[IAnchor[NT], Fraction]]:
    return [(view.left_anchor, conf.x), (view.top_anchor, conf.y), (view.width_anchor, conf.width), (view.height_anchor, conf.height)]