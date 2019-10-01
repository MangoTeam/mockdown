from __future__ import annotations

import operator
from abc import ABCMeta, abstractmethod
from dataclasses import dataclass, field, replace, asdict
from typing import Optional, Iterable, Tuple

import pandas as pd

from mockdown.model import AnchorID, IAnchor, IView


@dataclass(frozen=True)
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

    op: {operator.eq, operator.le, operator.ge} = field(default=operator.eq)

    priority: int = field(default=1000)
    sample_count: int = field(default=0)

    def __post_init__(self):
        self.validate_constants()

    def __str__(self):
        op_str = {
            operator.eq: '=',
            operator.le: '≤',
            operator.ge: '≥'
        }[self.op]

        a_str = "" if self.a == 1.0 else f"{self.a} * "
        b_str = "" if self.b == 0 else f" {'+' if self.b >= 0 else '-'} {abs(self.b)}"

        return (f"{str(self.y)} {op_str} {a_str}{str(self.x)}{b_str}"
                f"(priority={self.priority}, samples={self.sample_count}, kind={self.kind})")

    @property
    def is_abstract(self):
        return self.sample_count == 0

    @property
    @abstractmethod
    def kind(self): ...

    @abstractmethod
    def validate_constants(self): ...

    def validate(self, x: Optional[IAnchor], y: IAnchor):
        assert self.x == x.identifier and self.y == y.identifier, \
            "Constraints must be trained on matching anchors."

        xv, yv = x.view, y.view

        assert xv.is_sibling_of(yv) or xv.is_parent_of(yv) or xv.is_child_of(yv), \
            "Constraints must be between siblings or parent/children."

        xa, ya = x.attribute, y.attribute

        assert xa.is_compatible(ya), \
            "Constraints must be between compatible anchors."

    def train(self, x: Optional[IAnchor], y: IAnchor):
        self.validate(x, y)

    def train_many(self, *pairs: Iterable[Tuple[Optional[IAnchor], IAnchor]]):
        constraint = self
        for x, y in pairs:
            constraint = constraint.train(x, y)
        return constraint

    def _anchors_in_view(self, view):
        x_anchor = view.get_anchor(self.x) if self.x else None
        y_anchor = view.get_anchor(self.y)

        return x_anchor, y_anchor

    def train_view(self, view: IView):
        """A convenience training method that also does the lookup."""
        return self.train(*self._anchors_in_view(view))

    def train_view_many(self, *views: IView):
        """Like `train_view`, but accepts multiple views."""
        return self.train_many(*map(self._anchors_in_view, views))

    def to_dict(self) -> dict:
        return {
            'y': str(self.y),
            'op': {
                operator.eq: '=',
                operator.le: '≤',
                operator.ge: '≥'
            }[self.op],
            'a': self.a,
            'x': str(self.x),
            'b': self.b,
            'sample_count': self.sample_count,
            'priority': self.priority,
            'kind': self.kind
        }

    @classmethod
    def from_dict(cls, d):
        kind = d.pop('kind')

        x_id = AnchorID.from_str(d.pop('x'))
        y_id = AnchorID.from_str(d.pop('y'))

        if kind == 'spacing':
            return SpacingConstraint(x=x_id, y=y_id, **d)
        elif kind == 'alignment':
            return AlignmentConstraint(x=x_id, y=y_id, **d)

    def to_series(self) -> pd.Series:
        return pd.Series(self.to_dict)

    @staticmethod
    def set_to_dataframe(*constraints: IConstraint):
        rows = map(lambda c: c.to_dict(), constraints)
        df = pd.DataFrame(rows)
        return df


class PositionConstraint(IConstraint):
    @property
    def kind(self):
        return "position"

    def validate_constants(self):
        assert self.a == 1.0, \
            "Position constraints musy not have not a non-identity multiplier."

    def validate(self, x: Optional[IAnchor], y: IAnchor):
        super().validate(x, y)

        assert x is not None, \
            "Spacing constraints must not have only one anchor."

    def train(self, x: Optional[IAnchor], y: IAnchor):
        super().train(x, y)

        new_b = y.value - x.value

        if not self.is_abstract:
            if self.op == operator.le:
                new_b = max(self.b, new_b)
            elif self.op == operator.ge:
                new_b = min(self.b, new_b)
            elif self.op == operator.eq:
                assert "unsupported operator: == (because of scary IEEE754 nonsense)"
            # new_b = new_b if self.op(self.b, new_b) else self.b

        return replace(self, b=new_b, sample_count=self.sample_count + 1)


class SpacingConstraint(PositionConstraint):
    @property
    def kind(self):
        return "spacing"


class AlignmentConstraint(PositionConstraint):
    @property
    def kind(self):
        return "alignment"
