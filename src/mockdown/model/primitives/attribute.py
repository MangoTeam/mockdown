from __future__ import annotations

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
        h_attrs = {Attribute.LEFT, Attribute.RIGHT, Attribute.CENTER_X}
        v_attrs = {Attribute.TOP, Attribute.BOTTOM, Attribute.CENTER_Y}
        s_attrs = {Attribute.WIDTH, Attribute.HEIGHT}

        return self in h_attrs and other in h_attrs \
               or self in v_attrs and other in v_attrs \
               or self in s_attrs and other in s_attrs
