from enum import Enum

from .typing import Priority

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

