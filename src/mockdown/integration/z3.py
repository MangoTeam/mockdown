from z3 import z3  # type: ignore

from ..constraint import IConstraint
from ..model import IAnchorID


def anchor_id_to_z3_var(anchor_id: IAnchorID, suffix: int) -> z3.Var:
    return z3.Real(str(anchor_id) + "_" + str(suffix))


def constraint_to_z3_expr(constraint: IConstraint, suffix: int) -> z3.ExprRef:
    yv = anchor_id_to_z3_var(constraint.y_id, suffix)
    rhs = constraint.b

    # removal note: fudge factor/linearize not necessary now that we have rationals only – Dylan
    if constraint.x_id:
        xv = anchor_id_to_z3_var(constraint.x_id, suffix)
        return constraint.op(yv, xv * constraint.a + rhs)
    else:
        return constraint.op(yv, rhs)
