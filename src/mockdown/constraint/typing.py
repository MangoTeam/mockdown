from __future__ import annotations

from abc import abstractmethod
from enum import Enum
from typing import Any, Dict, Optional, Protocol, Set, Tuple, TypeVar

import sympy as sym

from mockdown.model import IAnchorID

T = TypeVar('T')


class IComparisonOp(Protocol[T]):
    # This weird naming makes mypy happy (aligns with operator.eq, resources)
    def __call__(self, __a: T, __b: T) -> T: ...


Priority = Tuple[int, int, int]
PRIORITY_REQUIRED: Priority = (1000, 1000, 1000)
PRIORITY_STRONG: Priority = (1, 0, 0)
PRIORITY_MEDIUM: Priority = (0, 1, 0)
PRIORITY_WEAK: Priority = (0, 0, 1)


class ConstraintKind(Enum):
    _ignore_ = ['constant_forms',
                'add_only_forms',
                'mul_only_forms',
                'general_forms',
                'position_kinds',
                'size_kinds']

    # y = x + b, where y.attr and x.attr in {left, right, top, bottom}
    POS_LTRB_OFFSET = 'pos_lrtb_offset'

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

    # # y = ax + b, where y.attr = width and x.attr = height, and y = x, b != 0.
    SIZE_ASPECT_RATIO_GENERAL = 'size_aspect_ratio_general'

    @property
    def is_constant_form(self) -> bool:
        return self in ConstraintKind.constant_forms

    @property
    def is_add_only_form(self) -> bool:
        return self in ConstraintKind.add_only_forms

    @property
    def is_mul_only_form(self) -> bool:
        return self in ConstraintKind.mul_only_forms

    @property
    def is_general_form(self) -> bool:
        return self in ConstraintKind.general_forms

    @property
    def is_position_kind(self) -> bool:
        return self in ConstraintKind.position_kinds

    @property
    def is_size_kind(self) -> bool:
        return self in ConstraintKind.size_kinds


ConstraintKind.constant_forms = frozenset({
    ConstraintKind.SIZE_CONSTANT,
    ConstraintKind.SIZE_CONSTANT_BOUND
})

ConstraintKind.add_only_forms = frozenset({
    ConstraintKind.POS_LTRB_OFFSET,
    ConstraintKind.SIZE_OFFSET,
})

ConstraintKind.mul_only_forms = frozenset({
    ConstraintKind.SIZE_RATIO,
    ConstraintKind.SIZE_ASPECT_RATIO,
})

ConstraintKind.general_forms = frozenset({
    ConstraintKind.SIZE_RATIO_GENERAl,
    ConstraintKind.SIZE_ASPECT_RATIO_GENERAL
})

ConstraintKind.position_kinds = frozenset({
    ConstraintKind.POS_LTRB_OFFSET,
    ConstraintKind.POS_CENTERING
})

ConstraintKind.size_kinds = frozenset({
    ConstraintKind.SIZE_OFFSET,
    ConstraintKind.SIZE_RATIO,
    ConstraintKind.SIZE_CONSTANT,
    ConstraintKind.SIZE_ASPECT_RATIO
})


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
    def is_template(self) -> bool:
        return self.sample_count == 0

    @property
    def is_required(self) -> bool:
        return self.priority == PRIORITY_REQUIRED

    @property
    def resolves_ambiguity(self) -> bool:
        return (not self.is_required) and self.kind == ConstraintKind.SIZE_CONSTANT

    def to_expr(self) -> sym.Expr: ...

    def to_dict(self) -> Dict[str, str]: ...

    def __repr__(self) -> str: ...

    def __eq__(self, other: object) -> bool: ...

    def __hash__(self) -> int: ...
