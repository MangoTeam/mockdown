from __future__ import annotations

from enum import Enum
from typing import Any, Dict, Optional, Protocol, Set, Tuple, TypeVar

import sympy as sym

from mockdown.model import IAnchorID

T = TypeVar('T')


class IComparisonOp(Protocol[T]):
    # This weird naming makes mypy happy (aligns with operator.eq, etc)
    def __call__(self, __a: T, __b: T) -> T: ...


Priority = Tuple[int, int, int]
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

    # # y = ax + b, where y.attr and x.attr in {width, height}, b != 0.
    SIZE_RATIO_GENERAl = 'size_ratio_general'

    # y = b, where y.attr in {width, height}
    SIZE_CONSTANT = 'size_constant'

    # y = b, where y.attr in {width, height} but a priority-resolvable bound.
    # Note: should only be emitted when values are too far apart (noisy?) to
    # determine any more reasonable candidate.
    SIZE_CONSTANT_BOUND = 'size_constant_bound'

    # y = ax, where y.attr = width and x.attr = height, and y = x
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


class IConstraint:
    kind: ConstraintKind

    y_id: IAnchorID
    x_id: Optional[IAnchorID]

    a: sym.Rational
    b: sym.Rational

    op: IComparisonOp[Any]
    priority: Priority

    sample_count: int

    @property
    def is_falsified(self) -> bool:
        return False

    @property
    def is_template(self) -> bool:
        return self.sample_count == 0

    @property
    def is_required(self) -> bool:
        return self.priority == PRIORITY_REQUIRED

    @property
    def resolves_ambiguity(self) -> bool:
        return self.is_required and \
               self.kind == ConstraintKind.SIZE_CONSTANT

    def to_expr(self) -> sym.Expr: ...

    def to_dict(self) -> Dict[str, str]: ...

    def __repr__(self) -> str: ...

    def __eq__(self, other: object) -> bool: ...

    def __hash__(self) -> int: ...
