from __future__ import annotations

import operator
from dataclasses import dataclass, field
from fractions import Fraction
from typing import Any, Dict, Optional, final

from mockdown.constraint.typing import ConstraintKind, IComparisonOp, IConstraint, PRIORITY_REQUIRED, Priority
from mockdown.model import IAnchorID


@final
@dataclass(eq=True, frozen=True)
class ConstantConstraint(IConstraint):
    """
    Constraint of the form y = b
    """
    kind: ConstraintKind

    y_id: IAnchorID
    x_id: Optional[IAnchorID] = field(default=None, init=False)

    a: Fraction = field(default=Fraction('0'), init=False)
    b: Fraction = Fraction('0')

    op: IComparisonOp[Any] = operator.eq
    priority: Priority = PRIORITY_REQUIRED

    sample_count: int = 0

    def to_dict(self) -> Dict[str, str]:
        return {
            'y': str(self.y_id),
            'op': {
                operator.eq: '=',
                operator.le: '≤',
                operator.ge: '≥'
            }[self.op],
            'a': str(self.a),
            'b': str(self.b),
            'priority': str(self.priority),
            'kind': self.kind.value
        }


@final
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

    op: IComparisonOp[Any] = operator.eq
    priority: Priority = PRIORITY_REQUIRED

    sample_count: int = 0

    def to_dict(self) -> Dict[str, str]:
        return {
            'y': str(self.y_id),
            'op': {
                operator.eq: '=',
                operator.le: '≤',
                operator.ge: '≥'
            }[self.op],
            'a': str(self.a),
            'x': str(self.x_id),
            'b': str(self.b),
            'priority': str(self.priority),
            'kind': self.kind.value
        }
