from abc import ABCMeta, abstractmethod
from dataclasses import dataclass, field
from typing import Optional

from mockdown.model import AnchorID, IAnchor


@dataclass
class IConstraint(metaclass=ABCMeta):
    """
    A general constraint of the form y = a * x + b.

    A constraint with no samples is 'abstract',
    which is more or less like Daikon's 'prototype' invariants.
    """
    x: Optional[AnchorID]
    y: AnchorID

    a: float = field(default=1.0)
    b: int = field(default=0)

    sample_count: int = field(default=0)

    def __post_init__(self):
        self.validate_constants()

    @property
    def is_abstract(self):
        return self.sample_count == 0

    @abstractmethod
    def validate_constants(self): ...

    def validate(self, x: Optional[IAnchor], y: IAnchor):
        xv = x.view
        yv = y.view

        assert xv.is_sibling_of(yv) or xv.is_parent_of(yv), \
            "Constraints must be between siblings or parent/children."

        xa = x.attribute
        ya = y.attribute

        # todo: attribute validation

    def train(self, x: Optional[IAnchor], y: IAnchor):
        self.validate(x, y)


class PositionConstraint(IConstraint):
    def validate_constants(self):
        assert self.a == 1.0, \
            "Position constraints may not have not a non-identity multiplier."

    def validate(self, x: Optional[IAnchor], y: IAnchor):
        super().validate(x, y)

    def train(self, x: Optional[IAnchor], y: IAnchor):
        super().train(x, y)


class SpacingConstraint(PositionConstraint):
    pass


class AlignmentConstraint(PositionConstraint):
    pass
