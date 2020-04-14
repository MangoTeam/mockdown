from mockdown.constraint import IConstraint


def anchor_equiv(c1: IConstraint, c2: IConstraint):
    """
    Equivalence modulo anchors.
    """
    return c1.y_id == c2.y_id and c1.x_id == c2.x_id
