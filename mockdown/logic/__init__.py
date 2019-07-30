from dataclasses import dataclass
from enum import Enum
from importlib import resources
from typing import List, Tuple, Optional, Generator

from pyswip import Prolog

from ..view import View, Anchor


@dataclass
class ConstrainablePair:
    """
    A constraint of the form:
    anchor1 = a * anchor_2 + b

    anchor2 can potentially be None, e.g. for size assignments:
        foo.width = 100
    """

    class Kind(Enum):
        SPACING = 'spacing'
        ALIGNMENT = 'alignment'

    kind: Kind
    anchor1: Anchor
    anchor2: Optional[Anchor]

    @staticmethod
    def spacing(anchor1: Anchor, anchor2: Anchor) -> 'ConstrainablePair':
        return ConstrainablePair(ConstrainablePair.Kind.SPACING, anchor1, anchor2)

    @staticmethod
    def alignment(anchor1: Anchor, anchor2: Anchor) -> 'ConstrainablePair':
        return ConstrainablePair(ConstrainablePair.Kind.ALIGNMENT, anchor1, anchor2)


def constraint_pairs(root: View, visibilities: List[Tuple[Anchor, Anchor]]) -> Generator[ConstrainablePair, None, None]:
    """
    Computes the valid ((view, attr), (view, attr)) pairs for various
    types of constraints.
    """

    # Note: Prolog is a singleton!
    prolog = Prolog()
    try:
        # Load static terms/predicates.
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

        for vis in visibilities:
            [a1, a2] = vis
            a1_term = f"anchor('{a1.view.name}', '{a1.attribute}')"
            a2_term = f"anchor('{a2.view.name}', '{a2.attribute}')"
            prolog.assertz(f"visible({a1_term}, {a2_term})")

        # todo: Post-process output? Necessary?

        for answer in prolog.query("spacing(V, A, W, B)"):
            v, a, w, b = [answer[k] for k in ('V', 'A', 'W', 'B')]

            anchor1 = getattr(root.get(v, include_self=True, deep=True), f"{a}_anchor")
            anchor2 = getattr(root.get(w, include_self=True, deep=True), f"{b}_anchor")

            yield ConstrainablePair.spacing(anchor1, anchor2)

        for answer in prolog.query("alignment(V, A, W, B)"):
            v, a, w, b = [answer[k] for k in ('V', 'A', 'W', 'B')]

            anchor1 = getattr(root.get(v, include_self=True, deep=True), f"{a}_anchor")
            anchor2 = getattr(root.get(w, include_self=True, deep=True), f"{b}_anchor")

            yield ConstrainablePair.alignment(anchor1, anchor2)

    finally:
        # Cleanup dynamic predicates to avoid subsequent calls running in a 
        # polluted Prolog namespace.
        prolog.retractall('view(_)')
        prolog.retractall('parent(_,_)')

        prolog.retractall('visible(_,_)')
        pass
