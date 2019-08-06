from importlib import resources
from typing import List, Tuple, Generator

from pyswip import Prolog

from mockdown.model import IView, IAnchor, AnchorID
from mockdown.model.attribute import Attribute
from mockdown.model.constraint import SpacingConstraint, AlignmentConstraint, IConstraint


def valid_constraints(root: IView, visibilities: List[Tuple[IAnchor, IAnchor]]) \
        -> Generator[IConstraint, None, None]:
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
            a1_term = f"anchor('{a1.view.name}', '{a1.attribute.value}')"
            a2_term = f"anchor('{a2.view.name}', '{a2.attribute.value}')"
            prolog.assertz(f"visible({a1_term}, {a2_term})")

        # todo: Post-process output? Necessary?

        for answer in prolog.query("spacing(V, A, W, B)"):
            v, a, w, b = [answer[k] for k in ('V', 'A', 'W', 'B')]
            yield SpacingConstraint(AnchorID(v, Attribute(a)), AnchorID(w, Attribute(b)))

        for answer in prolog.query("alignment(V, A, W, B)"):
            v, a, w, b = [answer[k] for k in ('V', 'A', 'W', 'B')]
            yield AlignmentConstraint(AnchorID(v, Attribute(a)), AnchorID(w, Attribute(b)))

    finally:
        # Cleanup dynamic predicates to avoid subsequent calls running in a
        # polluted Prolog namespace.
        prolog.retractall('view(_)')
        prolog.retractall('parent(_,_)')

        prolog.retractall('visible(_,_)')
        pass
