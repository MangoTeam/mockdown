import kiwisolver  # type: ignore

from ..constraint import IConstraint


# todo: I had to add float(...) here because kiwisolver doesn't understand fractions. – Dylan
def constraint_to_kiwi(constraint: IConstraint, strength: str = 'required') -> kiwisolver.Constraint:
    yv = kiwisolver.Variable(str(constraint.y_id))
    if constraint.x_id:
        xv = kiwisolver.Variable(str(constraint.x_id))
        return constraint.op(yv, xv * (float(constraint.a))) | strength
    else:
        # print("me:", self)
        return constraint.op(yv, float(constraint.a)) | strength
