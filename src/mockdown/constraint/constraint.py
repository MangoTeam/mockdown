from __future__ import annotations

import operator
from dataclasses import dataclass, field
from fractions import Fraction
from typing import Any, Dict, Optional, final

from mockdown.constraint.typing import ConstraintKind, IComparisonOp, IConstraint, PRIORITY_REQUIRED, Priority
from mockdown.model import IAnchorID


def op_to_str(op: IComparisonOp[Any]):
    return {
        operator.eq: '=',
        operator.le: '≤',
        operator.ge: '≥'
    }[op]


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

    def __repr__(self) -> str:
        b = str(self.b) if self.sample_count > 0 else "_"
        return f"{self.y_id} {op_to_str(self.op)} b"

    def to_dict(self) -> Dict[str, str]:
        return {
            'y': str(self.y_id),
            'op': {
                operator.eq: '=',
                operator.le: '≤',
                operator.ge: '≥'
            }[self.op],
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

    def __repr__(self) -> str:
        a = str(self.a) if self.sample_count > 0 else "_"
        b = str(self.b) if self.sample_count > 0 else "_"
        return f"{self.y_id} {op_to_str(self.op)} {a} * {self.x_id} + {b}"

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
