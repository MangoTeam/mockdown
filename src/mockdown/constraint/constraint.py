from __future__ import annotations

import operator
from dataclasses import dataclass, field, replace
from typing import Any, Dict, Optional, final

import sympy as sym

from mockdown.constraint.types import ConstraintKind, IComparisonOp, IConstraint, PRIORITY_REQUIRED, Priority, \
    priority_to_str, op_to_str
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

    a: sym.Rational = field(default=sym.Rational(0), init=False)
    b: sym.Rational = sym.Rational(0)

    op: IComparisonOp[Any] = operator.eq
    priority: Priority = PRIORITY_REQUIRED

    sample_count: int = 0
    is_falsified: bool = False

    def subst(self,
              a: Optional[sym.Rational] = None,
              b: Optional[sym.Rational] = None,
              sample_count: int = 1) -> IConstraint:
        assert self.is_template
        assert sample_count != 0
        assert a is None or a == 0
        return replace(self, b=b, sample_count=sample_count)

    def __repr__(self) -> str:
        b = str(self.b) if not self.is_template else "_"
        return f"{self.y_id} {op_to_str(self.op)} {b}"

    def to_dict(self) -> Dict[str, str]:
        return {
            'y': str(self.y_id),
            'op': {
                operator.eq: '=',
                operator.le: '≤',
                operator.ge: '≥'
            }[self.op],
            'b': str(self.b),
            'strength': priority_to_str(self.priority),
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

    a: sym.Rational = sym.Rational(1)
    b: sym.Rational = sym.Rational(0)

    op: IComparisonOp[Any] = operator.eq
    priority: Priority = PRIORITY_REQUIRED

    sample_count: int = 0
    is_falsified: bool = False

    def subst(self,
              a: Optional[sym.Rational] = None,
              b: Optional[sym.Rational] = None,
              sample_count:int = 1) -> IConstraint:
        assert self.is_template
        assert sample_count != 0

        if a is None:
            a = self.a
        if b is None:
            b = self.b

        return replace(self, a=a, b=b, sample_count=sample_count)

    def __repr__(self) -> str:
        a = str(self.a) if not self.is_template else "_"
        b = str(self.b) if not self.is_template else "_"
        op = op_to_str(self.op)

        if self.kind.is_mul_only_form:
            return f"{self.y_id} {op} {a} * {self.x_id}"
        elif self.kind.is_add_only_form:
            return f"{self.y_id} {op} {self.x_id} + {b}"
        else:
            return f"{self.y_id} {op} {a} * {self.x_id} + {b}"

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
            'strength': priority_to_str(self.priority),
            'kind': self.kind.value
        }

# @final
# @dataclass(eq=True, frozen=True)
# class SymbolicConstraint(IConstraint):
#     kind: ConstraintKind
#     expr: Expr
#
#     def __post_init__(self):
#         pass
#
#     @property
#     def x_id(self) -> IAnchorID:
