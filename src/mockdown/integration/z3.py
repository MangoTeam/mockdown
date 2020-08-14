from typing import Dict, Iterable

import sympy as sym
from z3 import z3  # type: ignore

from mockdown.model.types import IAnchorID, IView
from mockdown.model.view.builder import IViewBuilder, ViewBuilder as V
from mockdown.types import NT
from ..constraint import IConstraint


def anchor_id_to_z3_var(anchor_id: IAnchorID, suffix: int) -> z3.Var:
    return z3.Real(str(anchor_id) + "_" + str(suffix))


def constraint_to_z3_expr(constraint: IConstraint, suffix: int) -> z3.ExprRef:
    yv = anchor_id_to_z3_var(constraint.y_id, suffix)
    rhs = constraint.b

    if constraint.x_id:
        xv = anchor_id_to_z3_var(constraint.x_id, suffix)
        return constraint.op(yv, xv * constraint.a + rhs)
    else:
        return constraint.op(yv, rhs)

def extract_model_valuations(model: z3.Model, idx: int, names: Iterable[str]) -> Dict[str, sym.Rational]:
    def get(name: str) -> sym.Rational:
        z3_name = name + "_" + str(idx)
        z3_names = [d.name() for d in model.decls()]
        if z3_name not in z3_names:
            raise Exception("missing lookup:", z3_name, z3_names)
        val = z3.Real(name + "_" + str(idx))
        out: sym.Rational = sym.Rational(model.get_interp(val).as_fraction())
        return out
    return {name: get(name) for name in names}

def load_view_from_model(model: z3.Model, idx: int, skeleton: IView[NT]) -> IView[sym.Rational]:

    def get(name: str) -> sym.Rational:
        val = z3.Real(name + "_" + str(idx))
        out: sym.Rational = sym.Rational(model.get_interp(val).as_fraction())
        return out
            
    def recurse(seed: IView[NT]) -> IViewBuilder:

        l, t = str(seed.left_anchor.id), str(seed.top_anchor.id)
        r, b = str(seed.right_anchor.id), str(seed.bottom_anchor.id)

        # left top right bottom
        rect = (get(l),get(t),get(r),get(b))

        children = [recurse(inner) for inner in seed.children]

        return V(name=seed.name, rect=rect, children=children)

    return recurse(skeleton).build(number_type=sym.Rational)