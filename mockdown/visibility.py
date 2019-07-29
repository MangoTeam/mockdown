from dataclasses import dataclass, field
from dominate import tags as html
from operator import attrgetter
from itertools import chain
from typing import List, Tuple

from intervaltree import Interval, IntervalTree
from more_itertools import pairwise

from .view import View, Edge

def interval_tree(root: View, primary_axis: str):  
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
        
        
def visible_pairs(view: View, deep=True) -> List[Tuple[Edge, Edge]]:
    """
    Compute visible (view, attr) pairs for the given view. 
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
    
    get_pos = attrgetter('position')

    pairs = []
    
    for x_ev in x_events:
        # Cast a vertical line through horizontal intervals.        
        data = sorted(map(attrgetter('data'), x_itree[x_ev]), key=get_pos)
        for pair in pairwise(data):
            if (pair[0].view.name == pair[1].view.name):
                continue
            pairs.append(pair)
        
    for y_ev in y_events:
        # Cast a horizontal line through vertical intervals.
        data = sorted(map(attrgetter('data'), y_itree[y_ev]), key=get_pos)
        for pair in pairwise(data):
            if (pair[0].view.name == pair[1].view.name):
                continue
            pairs.append(pair)
    
    if deep:
        for child in children:
            child_pairs = visible_pairs(child, deep=deep)
            pairs += child_pairs
    
    return pairs


def pair_to_css(pair: Tuple['Edge', 'Edge'], scale=1):
    [e1, e2] = pair
    v1 = e1.view
    v2 = e2.view
        
    style = [
        "position: absolute;"
        "box-sizing: border-box;"
        "border: 0.5px dashed red;"
    ]
                    
    if (e1.attribute in ['left', 'right']):
        assert e2.attribute in ['left', 'right']
        
        width = e2.position - e1.position
        
        if (v1 in v2.children):
            y_pos = v1.center_y
        elif (v2 in v1.children):
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
        
        
    if (e1.attribute in ['top', 'bottom']):
        assert e2.attribute in ['top', 'bottom']
        
        height = e2.position - e1.position
        
        if (v1 in v2.children):
            x_pos = v1.center_x
        elif (v2 in v1.children):
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


def pair_to_html(pair: Tuple['Edge', 'Edge'], scale=1):
    [e1, e2] = pair

    div_id = f"{e1.view.name}.{e1.attribute}-{e2.view.name}.{e2.attribute}"
    style = pair_to_css(pair, scale=scale)

    div = html.div(id=div_id, style=style)
    return div