from __future__ import annotations

import operator
from abc import abstractmethod
from fractions import Fraction
from typing import Protocol, Tuple, Any, Callable, Optional

from .constants import ConstraintKind
from ..model import IAnchorID

Priority = Tuple[int, int, int]
ComparisonOp = Callable[[Any, Any], Any]


class IConstraint(Protocol):
    @property
    @abstractmethod
    def x_id(self) -> Optional[IAnchorID]: ...

    @property
    @abstractmethod
    def y_id(self) -> IAnchorID: ...

    @property
    @abstractmethod
    def a(self) -> Fraction: ...

    @property
    @abstractmethod
    def b(self) -> Fraction: ...

    @property
    @abstractmethod
    def op(self) -> ComparisonOp: ...

    @property
    @abstractmethod
    def priority(self) -> Priority: ...

    @property
    @abstractmethod
    def kind(self) -> ConstraintKind: ...

    @property
    @abstractmethod
    def sample_count(self) -> int: ...

    def to_dict(self) -> dict:
        return {
            'y': str(self.y_id),
            'op': {
                operator.eq: '=',
                operator.le: '≤',
                operator.ge: '≥'
            }[self.op],
            'a': self.a,
            'x': str(self.x_id),
            'b': self.b,
            'meta': {
                'priority': self.priority,
                'kind': self.kind
            }
        }

