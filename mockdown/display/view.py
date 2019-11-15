from itertools import chain

import dominate.tags as html

from mockdown.display.constraint import constraint_to_html
from mockdown.display.visibility import visible_pair_to_html
from mockdown.model import IView


def view_label_html(view: IView) -> html.label:
    style = (
        "--left: 5px;"
        "--top: 5px;"
    )

    label = html.span(view.name, cls="mockdown-vis-label", style=style)
    return label


def view_to_html(view: IView, scale=1, is_root=False) -> html.div:
    style = (
        f"--left:   {scale * view.left}px;"
        f"--right:  {scale * view.right}px;"
        f"--top:    {scale * view.top}px;"
        f"--bottom: {scale * view.bottom}px;"
        f"--height: {scale * view.height}px;"
        f"--width:  {scale * view.width}px;"
    )

    class_str = f"mockdown-vis-view {'mockdown-vis-root' if is_root else ''}"
    div = html.div(cls=class_str, id=view.name, style=style)
    div.add(view_label_html(view))

    return div


def display_view(view: IView, visible_pairs=None, constraints=None, extra_styles=None, scale=1) -> html.div:
    if visible_pairs is None:
        visible_pairs = []

    if constraints is None:
        constraints = []

    style = (
        f"--width:  {scale * view.width}px;"
        f"--height: {scale * view.height}px;"
    )

    if extra_styles:
        style += extra_styles

    container = html.div(cls="mockdown-vis-root", style=style)

    container.add(view_to_html(view, scale=scale, is_root=True))
    for subview in chain(*map(iter, view.children)):
        container.add(view_to_html(subview, scale=scale))

    for pair in visible_pairs:
        container.add(visible_pair_to_html(pair, scale=scale))

    for constraint in constraints:
        el = constraint_to_html(constraint, view, scale=scale)
        if el is not None:
            container.add(el)

    return container

# def multi_view_container() -> html.div:
#     container = html.div(*layout_divs, style="display: flex; flex-direction: row; align-content: space-around;")
