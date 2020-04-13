from typing import Protocol, Optional, Tuple, Any, Callable

from ..model import IAnchorID

Priority = Tuple[int, int, int]
ComparisonOp = Callable[[Any, Any], Any]


class IConstraint(Protocol):
    x: Optional[IAnchorID]
    y: IAnchorID

    a: float
    b: int

    # Note: Any, not Bool, is intention.
    op: ComparisonOp
    priority: Priority
