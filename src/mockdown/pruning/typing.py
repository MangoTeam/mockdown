from typing import Callable, List, TypedDict, Optional, Protocol

from mockdown.model import IView
from mockdown.constraint import IConstraint


class ISizeBounds(TypedDict):
    min_w: Optional[int]
    min_h: Optional[int]
    max_w: Optional[int]
    max_h: Optional[int]


class IPruningMethod(Protocol):
    def __call__(self, cns: List[IConstraint]) -> List[IConstraint]: ...


PruningMethodFactory = Callable[[List[IView], ISizeBounds], IPruningMethod]
