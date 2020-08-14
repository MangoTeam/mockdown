from mockdown.model.types import IView
from mockdown.types import NT
from .types import IConstraint


# todo: rewrite constraint validation!

def check_against_view(view: IView[NT], constraint: IConstraint) -> bool:
    rhs = constraint.b
    lv = view.find_anchor(constraint.y_id)
    if lv:
        lhs = lv.value
        if constraint.x_id:
            rv = view.find_anchor(constraint.x_id)
            if rv:
                rhs += constraint.a * rv.value
            else:
                raise Exception("expected constraint x-value in view %s" % str(constraint.x_id))
        output: bool = constraint.op(lhs, rhs)
        return output
    else:
        raise Exception("expected constraint y-value in view %s" % str(lv))

    constraint.op(lv, 0)
    return True
