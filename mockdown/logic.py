import operator
from importlib import resources
from typing import List, Tuple, Generator

from pyswip import Prolog

from mockdown.model import IView, IAnchor, AnchorID
from mockdown.model.attribute import Attribute
from mockdown.model.constraint import SpacingConstraint, AlignmentConstraint, IConstraint
from mockdown.model.constraint.constraint import AbsoluteSizeConstraint, RelativeSizeConstraint, \
    AspectRatioSizeConstraint


def valid_constraints(root: IView, visibilities: List[Tuple[IAnchor, IAnchor]], debug = False) \
        -> Generator[IConstraint, None, None]:
    """
    Computes the valid constraint pairs (or singletons) for various
    types of constraints.
    """

    debug = True
    outfile = "debug.pl"


    # Note: Prolog is a singleton!
    prolog = Prolog()
    try:
        with open(outfile, 'w') as dbfile:
            # Load static terms/predicates.
            with resources.path(__package__, 'mockdown.pl') as path:
                prolog.consult(str(path))

            # Add dynamic terms/predicates.
            prolog.dynamic('view/1')
            prolog.dynamic('parent/2')
            prolog.dynamic('visible/2')

            for view in root:
                prolog.assertz(f"view('{view.name}')")
                if (debug): dbfile.write(f"view('{view.name}').\n")
                for child in view.children:
                    prolog.assertz(f"parent('{view.name}', '{child.name}')")
                    if (debug): dbfile.write(f"parent('{view.name}', '{child.name}').\n")

            for vis in visibilities:
                [a1, a2] = vis
                a1_term = f"anchor('{a1.view.name}', '{a1.attribute.value}')"
                a2_term = f"anchor('{a2.view.name}', '{a2.attribute.value}')"
                prolog.assertz(f"visible({a1_term}, {a2_term})")
                if (debug): dbfile.write(f"visible({a1_term}, {a2_term}).\n")

            # todo: Post-process output? Necessary?

            for answer in prolog.query("aspect_ratio_size(V)"):
                v, = [answer[k] for k in ('V',)]
                yield AspectRatioSizeConstraint(x=AnchorID(v, Attribute('height')),
                                                y=AnchorID(v, Attribute('width')),
                                                op=operator.eq)

            for answer in prolog.query("absolute_size(V, A)"):
                v, a = [answer[k] for k in ('V', 'A')]
                yield AbsoluteSizeConstraint(x=None, y=AnchorID(v, Attribute(a)), op=operator.le)
                yield AbsoluteSizeConstraint(x=None, y=AnchorID(v, Attribute(a)), op=operator.ge)

            for answer in prolog.query("parent_relative_size(V, A, W, B)"):
                v, a, w, b = [answer[k] for k in ('V', 'A', 'W', 'B')]
                yield RelativeSizeConstraint(x=AnchorID(v, Attribute(a)), y=AnchorID(w, Attribute(b)), op=operator.eq)

            for answer in prolog.query("spacing(V, A, W, B)"):
                v, a, w, b = [answer[k] for k in ('V', 'A', 'W', 'B')]
                yield SpacingConstraint(x=AnchorID(v, Attribute(a)), y=AnchorID(w, Attribute(b)), op=operator.le)
                yield SpacingConstraint(x=AnchorID(v, Attribute(a)), y=AnchorID(w, Attribute(b)), op=operator.ge)

            for answer in prolog.query("alignment(V, A, W, B)"):
                v, a, w, b = [answer[k] for k in ('V', 'A', 'W', 'B')]
                yield AlignmentConstraint(x=AnchorID(v, Attribute(a)), y=AnchorID(w, Attribute(b)), op=operator.le)
                yield AlignmentConstraint(x=AnchorID(v, Attribute(a)), y=AnchorID(w, Attribute(b)), op=operator.ge)

    finally:
        # Cleanup dynamic predicates to avoid subsequent calls running in a
        # polluted Prolog namespace.
        prolog.retractall('view(_)')
        prolog.retractall('parent(_,_)')

        prolog.retractall('visible(_,_)')
        pass
