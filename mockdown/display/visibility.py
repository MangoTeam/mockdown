from typing import Tuple

import dominate.tags as html

from ..view import Edge


def visible_pair_style(pair: Tuple[Edge, Edge], scale=1):
    [e1, e2] = pair
    v1 = e1.view
    v2 = e2.view

    style = [
        "position: absolute;"
        "box-sizing: border-box;"
        "border: 0.5px dashed red;"
    ]

    if e1.attribute in ['left', 'right']:
        assert e2.attribute in ['left', 'right']

        width = e2.position - e1.position

        if v1 in v2.children:
            y_pos = v1.center_y
        elif v2 in v1.children:
            y_pos = v2.center_y
        else:  # siblings
            y_pos = (v1.center_y + v2.center_y) / 2

        style += [
            f"left: {scale * e1.position}px;"
            f"right: {scale * e2.position}px;"
            f"top: {scale * y_pos}px;"
            f"bottom: {scale * y_pos}px;"
            f"width: {scale * width}px;"
            "height: 1px;"
        ]

    if e1.attribute in ['top', 'bottom']:
        assert e2.attribute in ['top', 'bottom']

        height = e2.position - e1.position

        if v1 in v2.children:
            x_pos = v1.center_x
        elif v2 in v1.children:
            x_pos = v2.center_x
        else:  # siblings
            x_pos = (v1.center_x + v2.center_x) / 2

        style += [
            f"left: {scale * x_pos}px;"
            f"right: {scale * x_pos}px;"
            f"top: {scale * e1.position}px;"
            f"bottom: {scale * e2.position}px;"
            "width: 1px;"
            f"height: {scale * height}px;"
        ]

    return "".join(style)


def visible_pair_to_html(pair: Tuple[Edge, Edge], scale=1):
    [e1, e2] = pair

    div_id = f"{e1.view.name}.{e1.attribute}-{e2.view.name}.{e2.attribute}"
    style = visible_pair_style(pair, scale=scale)

    div = html.div(id=div_id, style=style)
    return div
