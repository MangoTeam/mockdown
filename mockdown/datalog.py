from dataclasses import dataclass
from enum import Enum
from itertools import chain
from typing import List, Tuple

from pyDatalog import pyDatalog as pdl

import inspect

from .view import View, Anchor

class ConstraintKind(Enum):
    SPACING = 'spacing'
    ALIGNMENT = 'alignment'

@dataclass
class ConstraintPair:
    kind: ConstraintKind
    view1: View
    attr1: str
    view2: View
    attr2: str

def constraint_pairs(root: View, visible_pairs: List[Tuple[Anchor, Anchor]]) -> [ConstraintPair]:
    """
    Computes the valid ((view, attr), (view, attr)) pairs for various
    types of constraints.
    """

    
    pdl.create_terms('has_car, X')
    +locals()['has_car']('Mary')
    print(has_car(X))
    
    stack = inspect.stack()
    print(stack[1][0].f_locals.keys())

    
#         'anchor',
#         'sibling',
#         'visible',
#         'visible_sym',
#         'visible_horizontal',
#         'visible_vertical',
#         'alignable',
#         'alignable_sym',
#         'spacing',
#         'spacing_sib',
#         'spacing_pc',
#         'alignment'  