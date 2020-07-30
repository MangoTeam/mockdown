import kiwisolver  # type: ignore

from typing import Dict, List, cast, Iterator

from ..constraint import IConstraint

from mockdown.model.view.builder import IViewBuilder, ViewBuilder as V
from mockdown.model.primitives import Rect
import sympy as sym

from mockdown.model import IView, IAnchor, IAnchorID
from mockdown.typing import NT

def make_kiwi_env(view: List[IView[NT]]) -> Dict[str, kiwisolver.Variable]:
    return {str(anchor.id): anchor_to_kv(anchor) for box in view for anchor in box.anchors}

def anchor_to_kv(anchor: IAnchor[NT]) -> kiwisolver.Variable:
    return anchorid_to_kv(anchor.id)

def anchorid_to_kv(aid: IAnchorID) -> kiwisolver.Variable:
    return kiwisolver.Variable(str(aid))

def kiwi_lookup(x: IAnchor[NT], env: Dict[str, kiwisolver.Variable]) -> kiwisolver.Variable:
    return env[str(x.id)]

def add_linear_containment(solver: kiwisolver.Solver, env: Dict[str, kiwisolver.Variable], parent: IView[NT]) -> None:
    pl, pr = kiwi_lookup(parent.left_anchor, env), kiwi_lookup(parent.right_anchor, env)
    pt, pb = kiwi_lookup(parent.top_anchor, env), kiwi_lookup(parent.bottom_anchor, env)
    for child in parent.children:
        cl, cr = kiwi_lookup(child.left_anchor, env), kiwi_lookup(child.right_anchor, env)
        ct, cb = kiwi_lookup(child.top_anchor, env), kiwi_lookup(child.bottom_anchor, env)

        solver.addConstraint((cl >= pl) | 'required')
        solver.addConstraint((cr <= pr) | 'required')
        solver.addConstraint((ct >= pt) | 'required')
        solver.addConstraint((cb <= pb) | 'required')

def add_linear_axioms(solver: kiwisolver.Solver, targets: List[IView[NT]], env: Dict[str, kiwisolver.Variable]) -> None:
    for box in targets:
        strength = 'required'

        for anchor in box.anchors:
            kiwivar = kiwi_lookup(anchor, env)
            solver.addConstraint((kiwivar <= 10000.0) | 'weak')
            solver.addConstraint((kiwivar >= 0.0) | strength)
            

        

        w, h = kiwi_lookup(box.width_anchor, env),kiwi_lookup(box.height_anchor, env)
        l, r = kiwi_lookup(box.left_anchor, env), kiwi_lookup(box.right_anchor, env)
        b, t = kiwi_lookup(box.bottom_anchor, env), kiwi_lookup(box.top_anchor, env)
        c_x  = kiwi_lookup(box.center_x_anchor, env)
        c_y  = kiwi_lookup(box.center_y_anchor, env)

        # print('adding axioms for', w, h, l, r, b, t, c_x, c_y)

        solver.addConstraint((w == (r - l)) | strength)
        solver.addConstraint((h == (b - t)) | strength)
        solver.addConstraint((c_x == (l + r)/2.0) | strength) 
        solver.addConstraint((c_y == (t + b)/2.0) | strength)

def constraint_to_kiwi(constraint: IConstraint, env: Dict[str, kiwisolver.Variable], strength: str = 'required') -> kiwisolver.Constraint:
    yv = env[str(constraint.y_id)]
    if constraint.x_id:
        xv = env[str(constraint.x_id)]
        anum, adenom = map(int, constraint.a.as_numer_denom())
        bnum, bdenom = map(int, constraint.b.as_numer_denom())
        return constraint.op(yv * adenom * bdenom, xv * anum * bdenom + bnum * adenom) | strength
    else:
        # print("me:", self)
        bnum, bdenom = map(int, constraint.b.as_numer_denom())
        return constraint.op(yv * bdenom, bnum) | strength

def evaluate_constraints(view: IView[NT], top_rect: Rect[sym.Rational], constraints: List[IConstraint], strength: str = 'strong') -> IView[sym.Float]:
    solver = kiwisolver.Solver()
    env = make_kiwi_env([v for v in view])

    add_linear_axioms(solver, [v for v in view], env)
    for constr in constraints:
        solver.addConstraint(constraint_to_kiwi(constr, env, strength=strength))

    t_x, t_y = kiwi_lookup(view.left_anchor, env), kiwi_lookup(view.top_anchor, env)
    t_b, t_r = kiwi_lookup(view.bottom_anchor, env), kiwi_lookup(view.right_anchor, env)

    c_x, c_y, c_r, c_b = (top_rect.left, top_rect.top, top_rect.right, top_rect.bottom)
    
    solver.addConstraint((t_x == float(c_x)) | strength)
    solver.addConstraint((t_y == float(c_y)) | strength)
    solver.addConstraint((t_b == float(c_b)) | strength)
    solver.addConstraint((t_r == float(c_r)) | strength)

    solver.updateVariables()

    def get(anchor: IAnchor[NT]) -> float:
        kv = kiwi_lookup(anchor, env)
        return cast(float, kv.value())
            
    def recurse(seed: IView[NT]) -> IViewBuilder:

        l, t = seed.left_anchor, seed.top_anchor
        r, b = seed.right_anchor, seed.bottom_anchor

        # left top right bottom
        rect = (get(l),get(t),get(r),get(b))

        children = [recurse(inner) for inner in seed.children]

        return V(name=seed.name, rect=rect, children=children)

    return recurse(view).build(number_type=sym.Float)
