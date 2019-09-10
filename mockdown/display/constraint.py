from dominate import tags as html

from mockdown.display.util import horizontal_line_style, vertical_line_style
from mockdown.display.visibility import visible_pair_to_html
from mockdown.model import IView
from mockdown.model.attribute import Attribute
from mockdown.model.constraint import IConstraint, SpacingConstraint, AlignmentConstraint


# todo: rewrite to use new Constraint class

def spacing_constraint_to_html(constraint: IConstraint, view: IView, scale=1):
    e1 = view.get_anchor(constraint.x).edge
    e2 = view.get_anchor(constraint.y).edge

    # todo: does not handle center_x/center_y.
    # todo: is that an alignment concern..?

    return visible_pair_to_html((e1, e2), scale=scale)


def alignment_constraint_style(constraint: IConstraint, view: IView, scale=1):
    e1 = view.get_anchor(constraint.x).edge
    e2 = view.get_anchor(constraint.y).edge

    assert e1.attribute == e2.attribute

    union = (min(e1.interval[0], e2.interval[0]),
             max(e1.interval[1], e2.interval[1]))

    style = [
        "position: absolute;"
        "box-sizing: border-box;"
        "border: 0.5px dashed blue;"
    ]

    style_args = [union[0], union[1]]
    style_kwargs = {'scale': scale}

    if e1.attribute in {Attribute.LEFT, Attribute.RIGHT}:
        if e1.attribute is Attribute.LEFT:
            position = min(e1.position, e2.position)
            style_args.append(position)

        if e1.attribute is Attribute.RIGHT:
            position = max(e1.position, e2.position)
            style_args.append(position)

        style.append(vertical_line_style(*style_args, **style_kwargs))
    elif e1.attribute in {Attribute.TOP, Attribute.BOTTOM}:
        if e1.attribute is Attribute.TOP:
            position = min(e1.position, e2.position)
            style_args.append(position)

        if e1.attribute is Attribute.BOTTOM:
            position = max(e1.position, e2.position)
            style_args.append(position)

        style.append(horizontal_line_style(*style_args, **style_kwargs))
    else:
        raise NotImplementedError()

    return "".join(style)


def alignment_constraint_to_html(constraint: IConstraint, view: IView, scale=1):
    a1 = view.get_anchor(constraint.x)
    a2 = view.get_anchor(constraint.y)

    style = alignment_constraint_style(constraint, view, scale=scale)
    div_id = f"{a1.name}-{a2.name}"

    div = html.div(cls="mockdown-vis-constraint", id=div_id, style=style)

    return div


def constraint_to_html(pair: IConstraint, view: IView, scale=1):
    if isinstance(pair, SpacingConstraint):
        return spacing_constraint_to_html(pair, view, scale=scale)
    elif isinstance(pair, AlignmentConstraint):
        return alignment_constraint_to_html(pair, view, scale=scale)
    else:
        raise NotImplementedError()
