import kiwisolver

from ..constraint import AbstractConstraint


def constraint_to_kiwi(constraint: AbstractConstraint, strength: str = 'required') -> kiwisolver.Constraint:
    yv = kiwisolver.Variable(str(constraint.y))
    if constraint.x:
        xv = kiwisolver.Variable(str(constraint.x))
        return constraint.op(yv, xv * constraint.a) | strength
    else:
        # print("me:", self)
        return constraint.op(yv, constraint.a) | strength
