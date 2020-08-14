from mockdown.constraint import IConstraint
from mockdown.learning.types import IConstraintLearning


class ConstraintFalsified(Exception):
    def __init__(self, constraint: IConstraint):
        self.constraint = constraint
