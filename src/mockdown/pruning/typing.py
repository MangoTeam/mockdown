from typing import Callable, List, TypedDict, Optional, Protocol, Dict, Tuple, Iterable, Any, cast

from fractions import Fraction

from ..typing import NT
from ..integration import anchor_id_to_z3_var

from .util import anchor_equiv

from z3 import z3  # type: ignore

from dataclasses import fields, dataclass

from mockdown.model import IView
from mockdown.constraint import IConstraint, ConstraintKind

class ISizeBounds(TypedDict, total=False):
    min_w: Optional[Fraction]
    min_h: Optional[Fraction]
    max_w: Optional[Fraction]
    max_h: Optional[Fraction]
    min_x: Optional[Fraction]
    min_y: Optional[Fraction]
    max_x: Optional[Fraction]
    max_y: Optional[Fraction]

def bounds_from_json(it: Dict[Any, Any]) -> ISizeBounds:
    out = {}
    fields = ['min_w', 'min_h', 'max_w', 'max_h', 'min_x', 'max_x', 'min_y', 'max_y']

    for field in fields:
        out[field] = it.get(field)
    return cast(ISizeBounds, out)


class IPruningMethod(Protocol):
    def __call__(self, cns: List[IConstraint]) -> Tuple[List[IConstraint], Dict[str, Fraction], Dict[str, Fraction]]: ...

    def is_whole(self, c: IConstraint) -> bool:
        steps = [0.05 * x for x in range(20)]
        bestDiff: float = min([abs(s - c.a) for s in steps])
        return bestDiff <= 0.01

    def make_pairs(self, constraints: List[IConstraint]) -> List[Tuple[IConstraint, IConstraint]]:
        return [(c, cp) for c in constraints for cp in constraints if anchor_equiv(c, cp) and c.op != cp.op]

    def build_biases(self, constraints: List[IConstraint]) -> Dict[IConstraint, float]:
        scores = {c: 1.0 for c in constraints}

        pairs = self.make_pairs(constraints)
        # print([(x.shortStr(), y.shortStr()) for (x,y) in pairs][0])

        # reward specific constraint
        for c in constraints:
            score = 10
            # aspect ratios and size constraint are specific the more samples behind them
            if c.kind is ConstraintKind.SIZE_ASPECT_RATIO:
                # print(c, c.is_falsified)
                score = 1 if c.is_falsified else 100 * c.sample_count
            elif c.kind is ConstraintKind.SIZE_RATIO:
                # and doubly specific when the constants are nice
                if self.is_whole(c):
                    score = 1000 * c.sample_count
                else:
                    score = 100 * c.sample_count
            # positions are specific if they're paired and the pairs are close together
            elif c.kind in ConstraintKind.get_position_kinds():
                score = 1000
                # for simplicity we update pairs after this loop

            scores[c] = score

        for (l, r) in pairs:
            if l.kind in ConstraintKind.get_position_kinds():
                assert r.kind in ConstraintKind.get_position_kinds()

                diff = l.b + r.b
                # map > 500 => 10
                # 0 => 10000
                # everything else linearly
                upper = 500
                lower = 0
                if diff > upper:
                    score = 10
                else:
                    # a * upper + b = 10
                    # a * 0 +  b = 10000
                    # b = 10000, a  = -9990/upper
                    score = (-9990) / upper * diff + 10000
                    scores[l] = max(score, scores[l])
                    scores[r] = max(score, scores[r])

        return scores

    def add_containment_axioms(self, solver: z3. Optimize, confIdx: int, parent: IView[NT]) -> None:
        pl, pr = anchor_id_to_z3_var(parent.left_anchor.id, confIdx), anchor_id_to_z3_var(parent.right_anchor.id, confIdx)
        pt, pb = anchor_id_to_z3_var(parent.top_anchor.id, confIdx), anchor_id_to_z3_var(parent.bottom_anchor.id, confIdx)
        for child in parent.children:
            cl, cr = anchor_id_to_z3_var(child.left_anchor.id, confIdx), anchor_id_to_z3_var(child.right_anchor.id, confIdx)
            ct, cb = anchor_id_to_z3_var(child.top_anchor.id, confIdx), anchor_id_to_z3_var(child.bottom_anchor.id, confIdx)

            solver.add(cl >= pl)
            solver.add(cr <= pr)
            solver.add(ct >= pt)
            solver.add(cb <= pb)
        
    def add_layout_axioms(self, solver: z3.Optimize, confIdx: int, boxes: Iterable[IView[NT]]) -> None:

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
            solver.add(widthAx)
            solver.add(heightAx)
            solver.add(c_x == (l + r)/2) 
            solver.add(c_y == (t + b)/2)

            for anchor in box.anchors:
                solver.add(anchor_id_to_z3_var(anchor.id, confIdx) >= 0) 


PruningMethodFactory = Callable[[List[IView[NT]], ISizeBounds], IPruningMethod]
