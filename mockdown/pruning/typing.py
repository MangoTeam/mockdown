from typing import Callable, List, TypedDict, Optional

from mockdown.model import IView
from mockdown.constraint import AbstractConstraint


class ISizeBounds(TypedDict):
    min_w: Optional[str]
    min_h: Optional[str]
    max_w: Optional[str]
    max_h: Optional[str]


PruningMethod = Callable[[List[AbstractConstraint]], List[AbstractConstraint]]
PruningMethodFactory = Callable[[List[IView], ISizeBounds], PruningMethod]
