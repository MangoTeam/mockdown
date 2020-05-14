from typing import List, Tuple, cast, Any, Dict
from z3 import z3 #type: ignore

from fractions import Fraction

from math import floor, ceil

from dataclasses import dataclass
from .typing import ISizeBounds
from mockdown.model import IAnchor, IView
from mockdown.typing import NT, to_int, to_frac, round_frac, round_up, round_down

from collections import defaultdict

from mockdown.model.primitives import IRect, RRect, QRect

from mockdown.integration import anchor_id_to_z3_var



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

def from_rect(rect: IRect[NT]) -> Conformance:
    return Conformance(to_frac(rect.width), to_frac(rect.height), to_frac(rect.left), to_frac(rect.top))

def to_rect(conf: Conformance) -> QRect:
    return QRect(conf.x, conf.y, conf.x + conf.width, conf.y + conf.height)

def confs_to_bounds(lo_c: Conformance, hi_c: Conformance) -> ISizeBounds:
    return ISizeBounds({'min_w': lo_c.width, 'min_h': lo_c.height, 'max_w': hi_c.width, 'max_h': hi_c.height})

# def view_to_conf(view: IView[NT]) -> Conformance:


def conformance_range(lower: Conformance, upper: Conformance) -> List[Conformance]:

    # if not (lower < upper or lower == upper):
    #     if (lower > upper):
    #         tmp = lower
    #         lower = upper
    #         upper = lower
    #     else:
    #         raise Exception("incomparable arguments to range: [%s, %s]" % (lower, upper))
    
    # create 10 evenly spaced conformances on the range [min conf...max conf]
    scale = 10
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
