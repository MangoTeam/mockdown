from __future__ import annotations

from typing import FrozenSet, Any

from enum import Enum


class Attribute(Enum):
    LEFT = 'left'
    TOP = 'top'
    RIGHT = 'right'
    BOTTOM = 'bottom'
    CENTER_X = 'center_x'
    CENTER_Y = 'center_y'
    WIDTH = 'width'
    HEIGHT = 'height'

    def is_compatible(self, other: Attribute) -> bool:
        s_attrs = {Attribute.WIDTH, Attribute.HEIGHT}
        return self in h_attrs and other in h_attrs \
               or self in v_attrs and other in v_attrs \
               or self in s_attrs and other in s_attrs

    def is_size(self) -> bool:
        return self in {Attribute.WIDTH, Attribute.HEIGHT}

    def is_position(self) -> bool:
        return self in {Attribute.LEFT, Attribute.TOP, Attribute.RIGHT, Attribute.BOTTOM,
                        Attribute.CENTER_X, Attribute.CENTER_Y}

    def is_horizontal(self) -> bool:
        return self in {Attribute.LEFT, Attribute.RIGHT, Attribute.CENTER_X, Attribute.WIDTH}

    def is_vertical(self) -> bool:
        return self in {Attribute.TOP, Attribute.BOTTOM, Attribute.CENTER_Y, Attribute.HEIGHT}

    @staticmethod
    def is_dual_pair(a1: Attribute, a2: Attribute):
        if a1 == Attribute.RIGHT and a2 == Attribute.LEFT:
            return True
        if a1 == Attribute.BOTTOM and a2 == Attribute.TOP:
            return True
        return False

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


h_attrs: FrozenSet[Attribute] = frozenset({Attribute.LEFT, Attribute.RIGHT, Attribute.CENTER_X})
v_attrs: FrozenSet[Attribute] = frozenset({Attribute.TOP, Attribute.BOTTOM, Attribute.CENTER_Y})
