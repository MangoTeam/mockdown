import dominate.tags as html

from mockdown.display.constrainable import constrainable_pair_to_html
from mockdown.display.visibility import visible_pair_to_html
from ..view import View


def view_label_html(view: View) -> html.label:
    style = (
        "position: absolute;"
        "left: 5px;"
        "top: 5px;"
    )

    label = html.span(view.name, style=style)
    return label


def view_to_html(view: View, scale=1) -> html.div:
    style = (
        "position: absolute;"
        "box-sizing: border-box;"
        "border: 1px solid black;"
        f"left:   {scale * view.left}px;"
        f"right:  {scale * view.right}px;"
        f"top:    {scale * view.top}px;"
        f"bottom: {scale * view.bottom}px;"
        f"height: {scale * view.height}px;"
        f"width:  {scale * view.width}px;"
    )

    div = html.div(id=view.name, style=style)
    div.add(view_label_html(view))

    return div


def display_view(view: View, visible_pairs=None, constrainable_pairs=None, scale=1) -> html.div:
    if visible_pairs is None:
        visible_pairs = []

    if constrainable_pairs is None:
        constrainable_pairs = []

    style = (
        "font-size: 10px;"
        "position: relative;"
        f"width:  {scale * view.width}px;"
        f"height: {scale * view.height}px;"
    )

    container = html.div(id="container", style=style)

    for child in view:
        container.add(view_to_html(child, scale=scale))

    for pair in visible_pairs:
        container.add(visible_pair_to_html(pair, scale=scale))

    for pair in constrainable_pairs:
        container.add(constrainable_pair_to_html(pair, scale=scale))

    return container
