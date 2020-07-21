from typing import Any, Optional

from mockdown.constraint.constraint import ConstantConstraint, LinearConstraint
from mockdown.constraint.typing import ConstraintKind, IComparisonOp, IConstraint
from mockdown.model import IAnchorID
from mockdown.typing import unreachable

Kind = ConstraintKind


class ConstraintFactory:
    """
    Notes:
        - not an abstract factory (yet). No point.
        - could have some more complex system that doesn't rely on ConstraintKind.
    """

    def __init__(self) -> None:
        pass

    @staticmethod
    def create(kind: Kind,
               y_id: IAnchorID,
               x_id: Optional[IAnchorID] = None,
               op: Optional[IComparisonOp[Any]] = None) -> IConstraint:

        # Note: mypy isn't smart enough to understand `kind in { ... }`.
        # Also, can't use **kwargs for type safety reasons (dataclass will accept None!!!).
        if kind is kind is Kind.POS_LTRB_OFFSET \
                or kind is Kind.POS_CENTERING \
                or kind is Kind.SIZE_OFFSET \
                or kind is Kind.SIZE_RATIO \
                or kind is Kind.SIZE_ASPECT_RATIO:
            assert x_id is not None

            if op is not None:
                return LinearConstraint(kind=kind, y_id=y_id, x_id=x_id, op=op)
            else:
                return LinearConstraint(kind=kind, y_id=y_id, x_id=x_id)
        elif kind is Kind.SIZE_CONSTANT:
            assert x_id is None

            if op is not None:
                return ConstantConstraint(kind=kind, y_id=y_id, op=op)
            else:
                return ConstantConstraint(kind=kind, y_id=y_id)
        else:
            unreachable(kind)
