from mockdown.constraint import IConstraint


class ConstraintFalsified(Exception):
    def __init__(self, constraint: IConstraint):
        self.constraint = constraint