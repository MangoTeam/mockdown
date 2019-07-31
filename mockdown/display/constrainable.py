from dominate import tags as html

from .util import horizontal_line_style, vertical_line_style
from ..constrainable import ConstrainablePair
from ..display.visibility import visible_pair_to_html


def spacing_constrainable_pair_to_html(pair: ConstrainablePair, scale=1):
    e1 = pair.anchor1.edge
    e2 = pair.anchor2.edge

    # todo: does not handle center_x/center_y.
    # todo: is that an alignment concern..?

    return visible_pair_to_html((e1, e2), scale=scale)


def alignment_constrainable_pair_style(pair: ConstrainablePair, scale=1):
    e1 = pair.anchor1.edge
    e2 = pair.anchor2.edge

    assert e1.attribute == e2.attribute
    assert e1.position == e2.position

    position = e1.position
    union = (min(e1.interval[0], e2.interval[0]),
             max(e1.interval[1], e2.interval[1]))

    style = [
        "position: absolute;"
        "box-sizing: border-box;"
        "border: 0.5px dashed blue;"
    ]

    style_args = (union[0], union[1], position)
    style_kwargs = {'scale': scale}

    if e1.attribute in ['left', 'right']:
        style.append(vertical_line_style(*style_args, **style_kwargs))
    elif e1.attribute in ['top', 'bottom']:
        style.append(horizontal_line_style(*style_args, **style_kwargs))
    else:
        raise NotImplementedError()

    return "".join(style)


def alignment_constrainable_pair_to_html(pair: ConstrainablePair, scale=1):
    a1 = pair.anchor1
    a2 = pair.anchor2

    style = alignment_constrainable_pair_style(pair, scale=scale)
    div_id = f"{a1.name}-{a2.name}"

    div = html.div(id=div_id, style=style)

    return div


def constrainable_pair_to_html(pair: ConstrainablePair, scale=1):
    if pair.kind == 'spacing':
        return spacing_constrainable_pair_to_html(pair, scale=scale)
    elif pair.kind == 'alignment':
        return alignment_constrainable_pair_to_html(pair, scale=scale)
    else:
        raise NotImplementedError()
