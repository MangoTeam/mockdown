from mockdown.constraint import IConstraint


def anchor_equiv(c1: IConstraint, c2: IConstraint) -> bool:
    """
    Equivalence modulo anchors.
    """
    return c1.y_id == c2.y_id and c1.x_id == c2.x_id


def short_str(cn: IConstraint) -> str:
    import operator
    op_str = {
        operator.eq: '=',
        operator.le: '≤',
        operator.ge: '≥'
    }[cn.op]

    if cn.x_id:
        a_str = "" if cn.a == 1.0 else f"{cn.a} * "
        b_str = "" if cn.b == 0 else f" {'+' if cn.b >= 0 else '-'} {abs(cn.b)}"
        return f"{str(cn.y_id)} {op_str} {a_str}{str(cn.x_id)}{b_str}"
    else:
        return f"{str(cn.y_id)} {op_str} {str(cn.b)}"
