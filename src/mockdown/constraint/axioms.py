from typing import List

import sympy as sym

from mockdown.model import IView
from mockdown.types import NT


def make_axioms(views: List[IView[NT]]) -> List[sym.Expr]:
    axioms: List[sym.Expr] = []
    for view in views:
        pass
    return axioms
