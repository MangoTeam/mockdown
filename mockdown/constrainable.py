from dataclasses import dataclass
from typing import Optional

from mockdown.view import Anchor


@dataclass
class ConstrainablePair:
    """
    A constraint of the form:
    anchor1 = a * anchor_2 + b

    anchor2 can potentially be None, e.g. for size assignments:
        foo.width = 100
    """

    SPACING = 'spacing'
    ALIGNMENT = 'alignment'

    kind: str
    anchor1: Anchor
    anchor2: Optional[Anchor]

    @staticmethod
    def spacing(anchor1: Anchor, anchor2: Anchor) -> 'ConstrainablePair':
        return ConstrainablePair(ConstrainablePair.SPACING, anchor1, anchor2)

    @staticmethod
    def alignment(anchor1: Anchor, anchor2: Anchor) -> 'ConstrainablePair':
        return ConstrainablePair(ConstrainablePair.ALIGNMENT, anchor1, anchor2)