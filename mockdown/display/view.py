import dominate.tags as html

from mockdown.display.constraint import constraint_to_html
from mockdown.display.visibility import visible_pair_to_html
from mockdown.model import IView


def view_label_html(view: IView) -> html.label:
    style = (
        "position: absolute;"
        "left: 5px;"
        "top: 5px;"
    )

    label = html.span(view.name, style=style)
    return label


def view_to_html(view: IView, scale=1) -> html.div:
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


def display_view(view: IView, visible_pairs=None, constraints=None, scale=1) -> html.div:
    if visible_pairs is None:
        visible_pairs = []

    if constraints is None:
        constraints = []

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

    for constraint in constraints:
        container.add(constraint_to_html(constraint, view, scale=scale))

    return container
