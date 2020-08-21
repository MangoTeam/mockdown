from __future__ import annotations

import operator
from abc import abstractmethod
from dataclasses import dataclass
from enum import Enum, EnumMeta
from typing import Any, Dict, Optional, Protocol, Set, Tuple, TypeVar, FrozenSet, runtime_checkable

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


def op_to_str(op: IComparisonOp[Any]) -> str:
    return {
        operator.eq: '=',
        operator.le: '≤',
        operator.ge: '≥'
    }[op]


def priority_to_str(p: Priority) -> str:
    return str(list(p))


class ConstraintKindMeta(EnumMeta):
    """
    This metaclass just serves to inform mypy of the class attributes on
    ConstraintKind we assign just below the class definition.
    It doesn't do anything at runtime.
    """
    constant_forms: FrozenSet[ConstraintKind]
    add_only_forms: FrozenSet[ConstraintKind]
    mul_only_forms: FrozenSet[ConstraintKind]
    general_forms: FrozenSet[ConstraintKind]
    position_kinds: FrozenSet[ConstraintKind]
    size_kinds: FrozenSet[ConstraintKind]


class ConstraintKind(Enum, metaclass=ConstraintKindMeta):
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

    @property
    def num_free_vars(self) -> int:
        if self.is_constant_form:
            return 0
        elif self.is_mul_only_form or self.is_add_only_form:
            return 1
        else:
            return 2

    def __ge__(self, other: Any) -> bool:
        if self.__class__ is other.__class__:
            return self.value >= other.value
        return NotImplemented

    def __gt__(self, other: Any) -> bool:
        if self.__class__ is other.__class__:
            return self.value > other.value
        return NotImplemented

    def __le__(self, other: Any) -> bool:
        if self.__class__ is other.__class__:
            return self.value <= other.value
        return NotImplemented

    def __lt__(self, other: Any) -> bool:
        if self.__class__ is other.__class__:
            return self.value < other.value
        return NotImplemented


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


@runtime_checkable
class IConstraint(Protocol):
    kind: ConstraintKind

    y_id: IAnchorID
    x_id: Optional[IAnchorID]

    a: sym.Rational
    b: sym.Rational

    op: IComparisonOp[Any]
    priority: Priority

    sample_count: int
    is_falsified: bool

    @property
    def is_template(self) -> bool:
        return self.sample_count == 0

    @property
    def is_required(self) -> bool:
        return self.priority == PRIORITY_REQUIRED

    @property
    def resolves_ambiguity(self) -> bool:
        return (not self.is_required) and self.kind == ConstraintKind.SIZE_CONSTANT

    @abstractmethod
    def subst(self,
              a: Optional[sym.Rational] = None,
              b: Optional[sym.Rational] = None,
              sample_count: int = 1) -> IConstraint:
        """Fill a template by substituting in the provided values."""

    def to_expr(self) -> sym.Expr:
        ...

    def to_dict(self) -> Dict[str, str]:
        ...

    def _to_tuple(self) -> Tuple[ConstraintKind, IAnchorID,
                                 Optional[IAnchorID],
                                 str, Priority, int, bool]:
        """Converts to a tuple. Used for comparisons. """
        return (
            self.kind,
            self.y_id,
            self.x_id,
            op_to_str(self.op),
            self.priority,
            self.sample_count,
            self.is_falsified
        )

    def __repr__(self) -> str:
        ...

    def __eq__(self, other: object) -> bool:
        ...

    def __hash__(self) -> int:
        ...

    def __ge__(self, other: Any) -> bool:
        if isinstance(other, IConstraint):
            return self._to_tuple() >= other._to_tuple()
        return NotImplemented

    def __gt__(self, other: Any) -> bool:
        if isinstance(other, IConstraint):
            return self._to_tuple() > other._to_tuple()
        return NotImplemented

    def __le__(self, other: Any) -> bool:
        if isinstance(other, IConstraint):
            return self._to_tuple() <= other._to_tuple()
        return NotImplemented

    def __lt__(self, other: Any) -> bool:
        if isinstance(other, IConstraint):
            return self._to_tuple() < other._to_tuple()
        return NotImplemented
