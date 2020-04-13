import operator

from z3 import z3

from ..constraint import ISCLOSE_TOLERANCE, IConstraint
from ..model import IAnchorID


def anchor_id_to_z3_var(anchor_id: IAnchorID, suffix: int, linearize: bool = False) -> z3.Var:
    if linearize:
        return z3.Int(str(anchor_id) + "_" + str(suffix))
    else:
        return z3.Real(str(anchor_id) + "_" + str(suffix))


def constraint_to_z3_expr(constraint: IConstraint, suffix: int, linearize: bool = False):
    yv = anchor_id_to_z3_var(constraint.y, suffix, linearize)
    rhs = constraint.b

    precision = 1000

    def clamp(x):
        return int(round(x, 3) * precision)

    if not constraint.op == operator.eq:
        # print('adding fudge factor')
        if constraint.op == operator.ge:
            rhs -= ISCLOSE_TOLERANCE
        else:
            rhs += ISCLOSE_TOLERANCE
    if constraint.x:
        xv = anchor_id_to_z3_var(constraint.x, suffix, linearize)
        if linearize:
            return constraint.op(z3.IntVal(precision) * yv, xv * clamp(constraint.a) + clamp(rhs))
        else:
            return constraint.op(yv, xv * constraint.a + rhs)
    else:
        if linearize:
            return constraint.op(z3.IntVal(precision) * yv, clamp(rhs))
        else:
            return constraint.op(yv, rhs)
