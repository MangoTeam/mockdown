from __future__ import annotations

import math
import operator
from abc import abstractmethod, ABC
from dataclasses import dataclass, field, replace, fields
from typing import Optional, Iterable, Tuple, List, Sequence

from .constants import ISCLOSE_TOLERANCE, PRIORITY_REQUIRED
from .typing import IConstraint, ComparisonOp, Priority
from ..model import IAnchorID, IAnchor, IView, Attribute


@dataclass(eq=True, frozen=True)
class AbstractConstraint(IConstraint):
    """
    A general constraint of the form y = a * x + b.

    A constraint with no samples is 'abstract',
    which is more or less like Daikon's 'prototype' invariants.
    """
    x: Optional[IAnchorID]
    y: IAnchorID

    a: float = field(default=1.0)
    b: int = field(default=0)

    op: ComparisonOp = field(default=operator.eq)

    priority: Priority = field(default=PRIORITY_REQUIRED)
    sample_count: int = field(default=0)

    is_falsified: bool = field(default=False)

    def vars(self):
        return {self.y.view_name} | {self.x.view_name} if self.x is not None else {}

    def __post_init__(self):
        assert self.op in {operator.eq, operator.le, operator.ge}, \
            "Only =, ≥, and ≤ are supported."
        self.validate_constants()

    # equal modulo operator and offset
    def anchor_equiv(self, other: AbstractConstraint):
        return self.y == other.y and self.x == other.x

    def short_str(self):
        op_str = {
            operator.eq: '=',
            operator.le: '≤',
            operator.ge: '≥'
        }[self.op]

        if self.x:
            a_str = "" if self.a == 1.0 else f"{self.a} * "
            b_str = "" if self.b == 0 else f" {'+' if self.b >= 0 else '-'} {abs(self.b)}"
            return f"{str(self.y)} {op_str} {a_str}{str(self.x)}{b_str}"
        else:
            return f"{str(self.y)} {op_str} {str(self.b)}"

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
    def kind(self):
        ...

    def validate_constants(self):
        assert self.a >= 0, "Constraints must have positive multipliers."

    def validate(self, x: Optional[IAnchor], y: IAnchor):
        self.validate_constants()

        if x is not None:
            assert self.x == x.id, "Constraints must be trained on matching anchors."
        assert self.y == y.id, "Constraints must be trained on matching anchors."

        if x is not None:
            xv, yv = x.view, y.view

            assert xv.is_sibling_of(yv) or xv.is_parent_of(yv) or xv.is_child_of(yv) or xv == yv, \
                f"Constraint {self.short_str()} must be between siblings or parent/children " \
                f"(or be the same element): {xv.name} <> {yv.name}, parents : {xv.parent.name}, {yv.parent.name}"

            xa, ya = x.attribute, y.attribute

            assert xa.is_compatible(ya), \
                "Constraints must be between compatible anchors."

    def train(self, x: Optional[IAnchor], y: IAnchor):
        assert not self.is_falsified, "Cannot train a falsified constraint."
        self.validate(x, y)

    def train_many(self, pairs: Sequence[Tuple[Optional[IAnchor], IAnchor]]):
        constraint = self
        for x, y in pairs:
            constraint = constraint.train(x, y)
            if constraint.is_falsified:
                break
        return constraint

    def _anchors_in_view(self, view):
        x_anchor = view.get_anchor(self.x) if self.x else None
        y_anchor = view.get_anchor(self.y)

        return x_anchor, y_anchor

    def train_view(self, view: IView):
        """A convenience training method that also does the lookup."""
        return self.train(*self._anchors_in_view(view))

    def train_view_many(self, views: IView):
        """Like `train_view`, but accepts multiple views."""
        return self.train_many(list(map(self._anchors_in_view, views)))

    @property
    def bounds_above(self) -> List[IAnchorID]:
        """Returns the variable(s) this constraint bounds above."""
        y = [self.y]
        x = [self.x] if self.x is not None else []

        if self.op == operator.le:
            return y
        elif self.op == operator.ge:
            return x
        elif self.op == operator.eq:
            return x + y

        assert False, "This should be unreachable. What have you done."

    @property
    def bounds_below(self) -> List[IAnchorID]:
        """Returns the variable(s) this constraint bounds below."""
        y = [self.y]
        x = [self.x] if self.x is not None else []

        if self.op == operator.le:
            return x
        elif self.op == operator.ge:
            return y
        elif self.op == operator.eq:
            return x + y

        assert False, "This should be unreachable. What have you done."

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
            'kind': self.kind,
            'bounds_above': list(map(str, self.bounds_above)),
            'bounds_below': list(map(str, self.bounds_below))
        }

    @classmethod
    def from_dict(cls, d):
        d = {**d}
        kind = d.pop('kind')

        x_id = IAnchorID.from_str(d.pop('x'))
        y_id = IAnchorID.from_str(d.pop('y'))

        # Don't pass any extra fields to the constructor (they will error).
        class_fields = {f.name for f in fields(cls)}
        init_fields = {k: v for k, v in d.items() if k in class_fields}

        if kind == 'spacing':
            return SpacingConstraint(x=x_id, y=y_id, **init_fields)
        elif kind == 'alignment':
            return AlignmentConstraint(x=x_id, y=y_id, **init_fields)

    # def to_series(self) -> pd.Series:
    #     return pd.Series(self.to_dict)
    #
    # @staticmethod
    # def set_to_dataframe(*constraint: IConstraint):
    #     rows = map(lambda c: c.to_dict(), constraint)
    #     df = pd.DataFrame(rows)
    #     return df


class PositionConstraint(AbstractConstraint, ABC):
    def validate_constants(self):
        super().validate_constants()
        assert self.a == 1.0, \
            "Position constraint must not have not a non-identity multiplier."

    def validate(self, x: Optional[IAnchor], y: IAnchor):
        super().validate(x, y)

        assert x is not None, \
            "Spacing constraint must not have only one anchor."

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


class SizeConstraint(AbstractConstraint, ABC):
    pass


class AbsoluteSizeConstraint(SizeConstraint):
    @property
    def kind(self):
        return "absolute_size"

    def validate_constants(self):
        super().validate_constants()
        assert self.a == 1.0, "Absolute size constraint must have a = 1."

    def validate(self, x: Optional[IAnchor], y: IAnchor):
        super().validate(x, y)

        assert x is None, \
            "Absolute size constraint must only have one anchor."

    def train(self, x: Optional[IAnchor], y: IAnchor):
        super().train(x, y)

        new_b = y.value

        if not self.is_abstract:
            if self.op == operator.le:
                new_b = max(self.b, new_b)
            elif self.op == operator.ge:
                new_b = min(self.b, new_b)
            elif self.op == operator.eq:
                assert "unsupported operator: == (because of scary IEEE754 nonsense)"

        return replace(self, b=new_b, sample_count=self.sample_count + 1)


class RelativeSizeConstraint(SizeConstraint):
    @property
    def kind(self):
        return "relative_size"

    def validate_constants(self):
        super().validate_constants()
        assert math.isclose(self.b, 0, rel_tol=ISCLOSE_TOLERANCE), "Relative size constraint must have b = 0."

    def validate(self, x: Optional[IAnchor], y: IAnchor):
        super().validate(x, y)
        assert x.view.is_parent_of(y.view), "Relative size constraint' x must be the parent of y."
        assert x.attribute == y.attribute, "Relative size constraint should be between the same attribute."

    def train(self, x: Optional[IAnchor], y: IAnchor):
        super().train(x, y)

        is_falsified = self.is_falsified
        if x.value == 0:
            print('error: zero x value in constraint', self.to_dict())
            assert False

        new_a = y.value / x.value

        if not self.is_abstract:
            if self.op == operator.eq:
                if not math.isclose(self.a, new_a, rel_tol=ISCLOSE_TOLERANCE):
                    new_a = self.a
                    is_falsified = True
            if self.op == operator.le:
                new_a = max(self.a, new_a)
            if self.op == operator.ge:
                new_a = min(self.a, new_a)

        return replace(self, a=new_a, is_falsified=is_falsified, sample_count=self.sample_count + 1)


class AspectRatioSizeConstraint(SizeConstraint):
    @property
    def kind(self):
        return "aspect_ratio"

    def validate_constants(self):
        super().validate_constants()
        assert self.b == 0, "Aspect ratio constraint should not have a constant offset."  # negotiable

    def validate(self, x: Optional[IAnchor], y: IAnchor):
        super().validate(x, y)
        assert x.view == y.view, "Aspect ratio constraint are between two anchors of the same view."
        assert y.attribute == Attribute.WIDTH and x.attribute == Attribute.HEIGHT, \
            "Aspect ratio constraint are always between width and height (in that order!)"

    def train(self, x: Optional[IAnchor], y: IAnchor):
        super().train(x, y)

        is_falsified = self.is_falsified
        new_a = y.value / x.value

        if not self.is_abstract:
            if self.op == operator.eq:
                if not math.isclose(self.a, new_a, rel_tol=ISCLOSE_TOLERANCE):
                    new_a = self.a
                    is_falsified = True
            if self.op == operator.le:
                new_a = max(self.a, new_a)
            if self.op == operator.ge:
                new_a = max(self.a, new_a)

        return replace(self, a=new_a, is_falsified=is_falsified, sample_count=self.sample_count + 1)
