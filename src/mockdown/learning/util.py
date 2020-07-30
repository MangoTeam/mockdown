import operator
from typing import Any

import sympy as sym

from mockdown.constraint.typing import IComparisonOp


def widen_bound(op: IComparisonOp[Any], old: sym.Number, new: sym.Number) -> sym.Number:
    if op == operator.le:
        mx = sym.Max(old, new)  # type: ignore
        assert isinstance(mx, sym.Number)
        return mx
    elif op == operator.ge:
        mn = sym.Min(old, new)  # type: ignore
        assert isinstance(mn, sym.Number)
        return mn
    else:
        raise Exception("unsupported operator")
