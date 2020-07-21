from collections import deque
from itertools import chain, tee
from operator import attrgetter
from typing import Any, Iterable, List, Sequence, Set, Tuple

from intervaltree import IntervalTree  # type: ignore

from mockdown.constraint import IConstraint
from mockdown.instantiation.typing import IConstraintInstantiator
from mockdown.instantiation.logic import valid_constraints

from mockdown.model import IEdge, IView
from mockdown.typing import NT


class VisibilityConstraintInstantiator(IConstraintInstantiator[NT]):
    def instantiate(self, examples: Sequence[IView[NT]]) -> Sequence[IConstraint]:
        edge_pair_sets = [
            visible_pairs(example, deep=True)
            for example
            in examples
        ]

        anchor_pair_sets = [
            [(e1.anchor, e2.anchor) for (e1, e2) in edge_pair_set]
            for edge_pair_set
            in edge_pair_sets
        ]

        constraint_sets = {
            valid_constraints(examples[i], anchor_pair_sets[i])
            for i
            in range(len(examples))
        }

        all_constraints: Set[IConstraint] = set()
        for constraint_set in constraint_sets:
            all_constraints = all_constraints.union(constraint_set)

        return list(all_constraints)


def pairwise(iterable: Iterable[Any]) -> Iterable[Tuple[Any, Any]]:
    a, b = tee(iterable)
    next(b, None)
    return zip(a, b)


def interval_tree(root: IView[NT], primary_axis: str, include_root: bool = True) -> IntervalTree:
    """
    Compute an interval tree for the given root view
    and it's immediate children. The primary axis is
    the axis along which the lines vary. 
    
    The query axis is the other axis.
    """
    assert primary_axis in ['x', 'y']

    tree = IntervalTree()

    view_iter = root.children
    if include_root:
        view_iter = list(chain([root], view_iter))

    for view in view_iter:
        if primary_axis == 'x':
            top_edge = view.top_edge
            bottom_edge = view.bottom_edge

            tree.addi(*top_edge.interval, top_edge)
            tree.addi(*bottom_edge.interval, bottom_edge)

        if primary_axis == 'y':
            left_edge = view.left_edge
            right_edge = view.right_edge

            tree.addi(*left_edge.interval, left_edge)
            tree.addi(*right_edge.interval, right_edge)

    return tree


def visible_pairs(view: IView[NT], deep: bool = True) -> List[Tuple[IEdge[NT], IEdge[NT]]]:
    """
    Compute visible (view, attr) pairs for the given view. 
    :param view: the root view from which to compute pairs.
    :param deep controls whether visible_pairs calls recursively or not.
    """
    root = view
    children = root.children

    # We build an interval tree for the horizontal and 
    # vertical line segments making up our view rects.

    # We do _not_ include the root view, as it interferes with
    # sorting later, and we can just tack it onto the beginning/end
    # of each query.
    x_itree = interval_tree(root, primary_axis='x', include_root=False)
    y_itree = interval_tree(root, primary_axis='y', include_root=False)

    # In a scan-line algorithm, "events" are the points of
    # interest where we cast a scan line and check along it.
    x_events = set(chain(*((view.left, view.right)
                           for view
                           in chain([root], children))))

    y_events = set(chain(*((view.top, view.bottom)
                           for view
                           in chain([root], children))))

    x_sort_key = attrgetter('view.center_x', 'position')
    y_sort_key = attrgetter('view.center_y', 'position')

    pairs = []

    for x_ev in x_events:
        # Cast a vertical line through horizontal intervals.
        data = deque(sorted(map(attrgetter('data'), x_itree[x_ev]), key=y_sort_key))
        data.appendleft(root.top_edge)
        data.append(root.bottom_edge)
        for pair in pairwise(data):
            if pair[0].view.name == pair[1].view.name:
                continue
            pairs.append(pair)
            pairs.append((pair[0].view.center_y_edge, pair[1].view.center_y_edge))

    for y_ev in y_events:
        # Cast a horizontal line through vertical intervals.
        data = deque(sorted(map(attrgetter('data'), y_itree[y_ev]), key=x_sort_key))
        data.appendleft(root.left_edge)
        data.append(root.right_edge)
        for pair in pairwise(data):
            if pair[0].view.name == pair[1].view.name:
                continue
            pairs.append(pair)
            pairs.append((pair[0].view.center_x_edge, pair[1].view.center_x_edge))

    if deep:
        for child in children:
            child_pairs = visible_pairs(child, deep=deep)
            pairs += child_pairs

    return pairs
