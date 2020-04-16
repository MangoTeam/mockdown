from __future__ import annotations

import operator
from dataclasses import dataclass, field
from fractions import Fraction
from typing import Optional

from mockdown.constraint.typing import IConstraint, ComparisonOp, Priority, ConstraintKind, PRIORITY_REQUIRED
from mockdown.model import IAnchorID


@dataclass(eq=True, frozen=True)
class ConstantConstraint(IConstraint):
    """
    Constraint of the form y = b
    """
    kind: ConstraintKind

    y_id: IAnchorID
    x_id: Optional[IAnchorID] = field(default=None, init=False)

    a: Fraction = Fraction('1')
    b: Fraction = Fraction('0')

    op: ComparisonOp = operator.eq
    priority: Priority = PRIORITY_REQUIRED

    sample_count: int = 0
    is_falsified: bool = False


@dataclass(eq=True, frozen=True)
class LinearConstraint(IConstraint):
    """
    Constraint of the form y = a * x + b.
    Notes: b may be 0, but a may not be.
    """
    kind: ConstraintKind

    y_id: IAnchorID
    x_id: IAnchorID

    a: Fraction = Fraction('1')
    b: Fraction = Fraction('0')

    op: ComparisonOp = operator.eq
    priority: Priority = PRIORITY_REQUIRED

    sample_count: int = 0
    is_falsified: bool = False


