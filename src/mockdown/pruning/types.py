import operator
from dataclasses import replace
from fractions import Fraction
from typing import Callable, List, TypedDict, Optional, Protocol, Dict, Tuple, Iterable, Any, cast, Sequence, Set

from more_itertools import first_true
from z3 import z3  # type: ignore

import sys

from mockdown.constraint import IConstraint, ConstraintKind
from mockdown.constraint.types import PRIORITY_STRONG
from mockdown.integration import anchor_id_to_z3_var, constraint_to_z3_expr
from mockdown.model import IView
from mockdown.types import NT
from .util import anchor_equiv


class ISizeBounds(TypedDict, total=False):
    min_w: Optional[Fraction]
    min_h: Optional[Fraction]
    max_w: Optional[Fraction]
    max_h: Optional[Fraction]
    min_x: Optional[Fraction]
    min_y: Optional[Fraction]
    max_x: Optional[Fraction]
    max_y: Optional[Fraction]

def validate_bounds(bounds: ISizeBounds, view: IView[NT]) -> bool:

    def get(fld: str, default: int) -> Fraction:
        return bounds.get(fld, Fraction(default)) or Fraction(default)

    # if view.height < bounds.get('min_h', : return False
    if view.width < get('min_w', 0): return False
    if view.height < get('min_h', 0): return False
    if view.left < get('min_x', 0): return False
    if view.top < get('min_y', 0): return False
    if view.width > get('max_w', sys.maxsize): return False
    if view.height > get('max_h', sys.maxsize): return False
    if view.left > get('max_x', sys.maxsize): return False
    if view.top > get('max_y', sys.maxsize): return False

    return True

def bounds_from_json(it: Dict[Any, Any]) -> ISizeBounds:
    out = {}
    fields = ['min_w', 'min_h', 'max_w', 'max_h', 'min_x', 'max_x', 'min_y', 'max_y']

    for field in fields:
        out[field] = it.get(field)
    return cast(ISizeBounds, out)


class IPruningMethod(Protocol):
    def __call__(self, cns: List[IConstraint]) -> Tuple[List[IConstraint], Dict[str, Fraction], Dict[str, Fraction]]: ...

    # def is_whole(self, c: IConstraint) -> bool:
    #     steps = [0.05 * x for x in range(20)]
    #     bestDiff: float = min([abs(s - c.a) for s in steps])
    #     return bestDiff <= 0.01

    def whole_score(self, c: IConstraint) -> int:
        score = 1
        if c.x_id:
            if c.a.p < 25:
                score *= 10
            if c.a.p < 10:
                score *= 10
            if c.a.p > 100:
                # we probably don't want this...
                return 1
        if c.b.p < 25:
            score *= 10
        if c.b.p < 10:
            score *= 10
        if c.b.p > 100:
            # we probably don't want this...
            return score
        return score

    def dump_constraints(self, path: str, view: IView[NT], cns: List[IConstraint]) -> None:
        solver = z3.Optimize()
        self.add_layout_axioms(solver, 0, view, x_dim=True, tracking=False)
        self.add_layout_axioms(solver, 0, view, x_dim=False, tracking=False)
        for ci, c in enumerate(cns):
            solver.assert_and_track(constraint_to_z3_expr(c, 0), f's{str(ci)}')
        with open(path, 'w') as outfile:
            print(solver.sexpr(), file=outfile)
        return
    def make_pairs(self, constraints: List[IConstraint]) -> List[Tuple[IConstraint, IConstraint]]:
        return [(c, cp) for c in constraints for cp in constraints if anchor_equiv(c, cp) and c.op != cp.op]


    def combine_bounds(self, constraints: List[IConstraint]) -> List[IConstraint]:
        output: Set[IConstraint] = set()
        for c in constraints:
            other = first_true(iterable=constraints, pred=lambda t: anchor_equiv(c, t) and c.op != t.op, default=c)
            if other != c and abs(other.b - c.b) < 5:
                output.add(replace(c, op=operator.eq, b=(other.b + c.b)/2, priority=PRIORITY_STRONG))
            else:
                output.add(c)
        return list(output)


    def merge_pairs(self, pairs: List[Tuple[IConstraint, IConstraint]]) -> List[IConstraint]:
        output: List[IConstraint] = []
        for a, b in pairs:
            if a.b == b.b:
                output.append(replace(a, op=operator.eq))
            else:
                output.append(a)
                output.append(b)
        return output

    def build_biases(self, constraints: List[IConstraint]) -> Dict[IConstraint, float]:
        scores = {c: 1.0 for c in constraints}


        # reward specific constraints
        for c in constraints:
            score = 1
            # aspect ratios and size constraint are specific the more samples behind them
            if c.kind is ConstraintKind.SIZE_ASPECT_RATIO:
                score = 1 if c.is_falsified else 100
            elif c.kind is ConstraintKind.SIZE_RATIO:
                score = 100
            elif c.kind.is_position_kind or c.kind is ConstraintKind.SIZE_OFFSET:

                if c.op == operator.eq:

                    diff = abs(c.b)
                    # map > 100 => 10
                    # 0 => 1000
                    # everything else linearly
                    upper = 25
                    lower = 0
                    if diff > upper:
                        score = 10
                    else:
                        score = (-990) / upper * diff + 1000
                else:
                    score = 10 # penalize leq/geq

            elif c.kind is ConstraintKind.SIZE_CONSTANT:

                if c.op == operator.eq:
                    score = 1000
                else:
                    score = 10 # penalize leq/geq

            scores[c] = int(score * self.whole_score(c)) # * c.sample_count

        return scores

    def add_containment_axioms(self, solver: z3. Optimize, confIdx: int, parent: IView[NT], x_dim: bool) -> None:
        pl, pr = anchor_id_to_z3_var(parent.left_anchor.id, confIdx), anchor_id_to_z3_var(parent.right_anchor.id, confIdx)
        pt, pb = anchor_id_to_z3_var(parent.top_anchor.id, confIdx), anchor_id_to_z3_var(parent.bottom_anchor.id, confIdx)
        for child in parent.children:
            cl, cr = anchor_id_to_z3_var(child.left_anchor.id, confIdx), anchor_id_to_z3_var(child.right_anchor.id, confIdx)
            ct, cb = anchor_id_to_z3_var(child.top_anchor.id, confIdx), anchor_id_to_z3_var(child.bottom_anchor.id, confIdx)

            # if child.left_anchor.value >= parent.left_anchor.value:

            if x_dim:
                solver.add(cl >= pl)
                # if child.right_anchor.value <= parent.right_anchor.value:
                solver.add(cr <= pr)
                # if child.top_anchor.value >= parent.top_anchor.value:
            else:
                solver.add(ct >= pt)
                # if child.bottom_anchor.value <= parent.bottom_anchor.value:
                solver.add(cb <= pb)

            self.add_containment_axioms(solver, confIdx, child, x_dim)
            
            
        
    def add_layout_axioms(self, solver: z3.Optimize, confIdx: int, boxes: Iterable[IView[NT]], x_dim: bool, tracking: bool = False) -> None:
        for box in boxes:
            w, h = anchor_id_to_z3_var(box.width_anchor.id, confIdx), \
                   anchor_id_to_z3_var(box.height_anchor.id, confIdx)
            l, r = anchor_id_to_z3_var(box.left_anchor.id, confIdx), \
                   anchor_id_to_z3_var(box.right_anchor.id, confIdx)
            t, b = anchor_id_to_z3_var(box.top_anchor.id, confIdx), \
                   anchor_id_to_z3_var(box.bottom_anchor.id, confIdx)
            c_x  = anchor_id_to_z3_var(box.center_x_anchor.id, confIdx)
            c_y  = anchor_id_to_z3_var(box.center_y_anchor.id, confIdx)
            widthAx = w == (r - l)
            heightAx = h == (b - t)

            # print('adding axioms:', widthAx, heightAx, w>=0, h >= 0)

            if tracking:
                if x_dim:
                    raise Exception('unimplemented')
                solver.assert_and_track(widthAx, f'{box.name}-wax-{str(confIdx)}')
                solver.assert_and_track(heightAx, f'{box.name}-hax-{str(confIdx)}')
                solver.assert_and_track(c_x == (l + r)/2, f'{box.name}-cx-{str(confIdx)}') 
                solver.assert_and_track(c_y == (t + b)/2, f'{box.name}-cy-{str(confIdx)}')

                for idx, anchor in enumerate(box.anchors):
                    solver.assert_and_track(anchor_id_to_z3_var(anchor.id, confIdx) >= 0, f'{box.name}-pos-{str(confIdx)}-{str(idx)}')
            else:
                if x_dim:
                    solver.add(widthAx)
                    solver.add(c_x == (l + r)/2) 
                    for anchor in box.x_anchors:
                        solver.add(anchor_id_to_z3_var(anchor.id, confIdx) >= 0)
                else:
                    solver.add(heightAx)
                    solver.add(c_y == (t + b)/2)
                    for anchor in box.y_anchors:
                        solver.add(anchor_id_to_z3_var(anchor.id, confIdx) >= 0)

    def filter_constraints(self, constraints: List[IConstraint], elim_uneq: bool = True) -> List[IConstraint]:
        constraints = [c for c in constraints if c.kind != ConstraintKind.SIZE_ASPECT_RATIO]
        constraints = self.combine_bounds(constraints)
        if elim_uneq: constraints = list(filter(lambda c: c.op == operator.eq, constraints))
        return constraints
                

            


PruningMethodFactory = Callable[[List[IView[NT]], ISizeBounds, bool], IPruningMethod]


class MarginPruner(IPruningMethod):
    def __init__(self, examples: Sequence[IView[NT]], bounds: ISizeBounds, unambig: bool):
        pass
    def __call__(self, cns: List[IConstraint]) -> Tuple[List[IConstraint], Dict[str, Fraction], Dict[str, Fraction]]:
        return (self.filter_constraints([c for c in cns if c.kind == ConstraintKind.POS_LTRB_OFFSET or c.kind == ConstraintKind.POS_LTRB_OFFSET], elim_uneq=False), {}, {})
            
class DynamicPruner(IPruningMethod):
    def __init__(self, examples: Sequence[IView[NT]], bounds: ISizeBounds, unambig: bool):
        pass
    def __call__(self, cns: List[IConstraint]) -> Tuple[List[IConstraint], Dict[str, Fraction], Dict[str, Fraction]]:
        return (self.filter_constraints([replace(c, priority=PRIORITY_STRONG) for c in cns]), {}, {})
