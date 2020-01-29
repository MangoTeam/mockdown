from typing import Tuple

import dominate.tags as html

from mockdown.model import IEdge
from mockdown.model.attribute import Attribute
from .util import horizontal_line_style, vertical_line_style


def visible_pair_style(pair: Tuple[IEdge, IEdge], scale=1):
    [e1, e2] = pair

    style = [
        "position: absolute;"
        "box-sizing: border-box;"
        "border: 0.5px dashed red;"
    ]

    overlap = (max(e1.interval[0], e2.interval[0]),
               min(e1.interval[1], e2.interval[1]))

    midpoint = (overlap[0] + overlap[1]) / 2

    style_args = (e1.position, e2.position, midpoint)
    style_kwargs = {'scale': scale}

    lr_attrs = {Attribute.LEFT, Attribute.RIGHT, Attribute.CENTER_X}
    tb_attrs = {Attribute.TOP, Attribute.BOTTOM, Attribute.CENTER_Y}

    if e1.attribute in lr_attrs:
        assert e2.attribute in lr_attrs
        style.append(horizontal_line_style(*style_args, **style_kwargs))
    elif e1.attribute in tb_attrs:
        assert e2.attribute in tb_attrs
        style.append(vertical_line_style(*style_args, **style_kwargs))
    else:
        # center_x, center_y?
        raise NotImplementedError()

    return "".join(style)


def visible_pair_to_html(pair: Tuple[IEdge, IEdge], scale=1):
    [e1, e2] = pair

    div_id = f"{e1.view.name}.{e1.attribute}-{e2.view.name}.{e2.attribute}"
    style = visible_pair_style(pair, scale=scale)

    div = html.div(id=div_id, style=style)
    return div
