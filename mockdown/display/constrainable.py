from ..constrainable import ConstrainablePair
from ..display.visibility import visible_pair_to_html


def spacing_constrainable_pair_to_html(constrainable: ConstrainablePair, scale=1):
    e1 = constrainable.anchor1.edge
    e2 = constrainable.anchor2.edge

    return visible_pair_to_html((e1, e2), scale=scale)


def constrainable_pair_to_html(constrainable: ConstrainablePair, scale=1):
    if constrainable.kind == 'spacing':
        return spacing_constrainable_pair_to_html(constrainable, scale=scale)
    else:
        raise NotImplementedError()

