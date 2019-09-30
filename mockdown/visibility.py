from itertools import chain
from operator import attrgetter
from typing import List, Tuple

from intervaltree import IntervalTree
from more_itertools import pairwise

from mockdown.model import IView, IEdge


def interval_tree(root: IView, primary_axis: str):
    """
    Compute an interval tree for the given root view
    and it's immediate children. The primary axis is
    the axis along which the lines vary. 
    
    The query axis is the other axis.
    """
    assert primary_axis in ['x', 'y']

    tree = IntervalTree()

    for view in chain([root], root.children):
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


def visible_pairs(view: IView, deep=True) -> List[Tuple[IEdge, IEdge]]:
    """
    Compute visible (view, attr) pairs for the given view. 
    :param view: the root view from which to compute pairs.
    :param deep controls whether visible_pairs calls recursively or not.
    """
    root = view
    children = root.children

    # We build an interval tree for the horizontal and 
    # vertical line segments making up our view rects.

    x_itree = interval_tree(root, primary_axis='x')
    y_itree = interval_tree(root, primary_axis='y')

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
        data = sorted(map(attrgetter('data'), x_itree[x_ev]), key=y_sort_key)
        for pair in pairwise(data):
            if pair[0].view.name == pair[1].view.name:
                continue
            pairs.append(pair)

    for y_ev in y_events:
        # Cast a horizontal line through vertical intervals.
        data = sorted(map(attrgetter('data'), y_itree[y_ev]), key=x_sort_key)
        for pair in pairwise(data):
            if pair[0].view.name == pair[1].view.name:
                continue
            pairs.append(pair)

    if deep:
        for child in children:
            child_pairs = visible_pairs(child, deep=deep)
            pairs += child_pairs

    return pairs
