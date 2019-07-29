import os
from dataclasses import dataclass
from enum import Enum
from importlib import resources
from itertools import chain
from typing import List, Tuple

from pyswip import Prolog, Functor, Variable, Query, call

from ..view import View, Anchor

class ConstraintKind(Enum):
    SPACING = 'spacing'
    ALIGNMENT = 'alignment'

@dataclass
class ConstraintPair:
    kind: ConstraintKind
    anchor1: Anchor
    anchor2: Anchor

def constraint_pairs(root: View, visible_pairs: List[Tuple[Anchor, Anchor]]) -> [dict]:
    """
    Computes the valid ((view, attr), (view, attr)) pairs for various
    types of constraints.
    """
    try:
        # Load static terms/predicates.
        prolog = Prolog()
        with resources.path(__package__, 'mockdown.pl') as path:
            prolog.consult(str(path))

        # Add dynamic terms/predicates.
        prolog.dynamic('view/1')
        prolog.dynamic('parent/2')
        prolog.dynamic('visible/2')

        for view in root:
            prolog.assertz(f"view('{view.name}')")
            for child in view.children:
                prolog.assertz(f"parent('{view.name}', '{child.name}')")
        
        for vis in visible_pairs:
            [a1, a2] = vis
            a1_term = f"anchor('{a1.view.name}', '{a1.attribute}')"
            a2_term = f"anchor('{a2.view.name}', '{a2.attribute}')"
            prolog.assertz(f"visible({a1_term}, {a2_term})")

        # todo: Post-process output? Necessary?

        return list(prolog.query("spacing(V, A, W, B)"))
    finally:
        # Cleanup dynamic predicates to avoid subsequent calls running in a 
        # polluted Prolog namespace.
        prolog.retractall('view(_)')
        prolog.retractall('parent(_,_)')
        prolog.retractall('visible(_,_)')
        pass