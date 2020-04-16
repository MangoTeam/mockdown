from __future__ import annotations

import operator
from abc import abstractmethod
from enum import Enum
from fractions import Fraction
from typing import Dict, Protocol, Tuple, Any, Callable, Optional, TypedDict

from ..model import IAnchorID

Priority = Tuple[int, int, int]
ComparisonOp = Callable[[Any, Any], Any]

ISCLOSE_TOLERANCE = 0.01  # maximum difference of 1%
PRIORITY_REQUIRED: Priority = (1000, 1000, 1000)
PRIORITY_STRONG: Priority = (1, 0, 0)
PRIORITY_MEDIUM: Priority = (0, 1, 0)
PRIORITY_WEAK: Priority = (0, 0, 1)


class ConstraintKind(Enum):
    # y = x + b, where y.attr and x.attr in {left, right, top, bottom}
    POS_LTRB_OFFSET = 'pos_lrtb_offset'

    # y = ax + b, where y.attr and x.attr in {left, right, top, bottom}
    POS_LTRB_GENERAL = 'pos_lrtb_general'

    # y = x, where y.attr and x.attr in {center_x, center_y}
    POS_CENTERING = 'pos_centering'

    # y = x + b, where y.attr and x.attr in {width, height}
    SIZE_OFFSET = 'size_offset'

    # y = ax, where y.attr and x.attr in {width, height}
    SIZE_RATIO = 'size_ratio'

    # y = b, where y.attr in {width, height}
    SIZE_CONSTANT = 'size_constant'

    # y = ax + b, where y.attr = width and x.attr = height, and y = x
    SIZE_ASPECT_RATIO = 'size_aspect_ratio'

    @classmethod
    def get_position_kinds(cls) -> Set[ConstraintKind]:
        return {cls.POS_LTRB_OFFSET,
                cls.POS_LTRB_GENERAL,
                cls.POS_CENTERING}

    # noinspection PyPep8Naming
    @classmethod
    def get_size_kinds(cls) -> Set[ConstraintKind]:
        return {cls.SIZE_OFFSET,
                cls.SIZE_RATIO,
                cls.SIZE_CONSTANT,
                cls.SIZE_ASPECT_RATIO}


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

    @property
    def is_falsified(self) -> bool:
        return False
