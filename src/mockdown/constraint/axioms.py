from typing import List

import sympy as sym

from mockdown.model import IView
from mockdown.typing import NT


def make_axioms(views: List[IView[NT]]) -> List[sym.Expr]:
    axioms = []
    for view in views:
        pass
    return axioms
