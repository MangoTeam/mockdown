from __future__ import annotations

from dataclasses import dataclass, field
from itertools import chain
from typing import List, Optional, Sequence

from .. import IView
from ..anchor import Anchor, AnchorID
from ..edge import Edge
from ..primitives import IRect, Attribute, ViewName
from ...typing import NT


@dataclass(frozen=True)
class View(IView[NT]):
    name: ViewName
    rect: IRect[NT]
    children: Sequence[View[NT]] = field(default_factory=list)
    parent: Optional[View[NT]] = field(default=None)

    def is_parent_of(self, view) -> bool:
        return view.parent == self

    def is_parent_of_name(self, name: ViewName) -> bool:
        return any([x.name == name for x in self.children])

    def is_child_of(self, view) -> bool:
        return self.parent == view

    def is_sibling_of(self, view) -> bool:
        comp = self.parent == view.parent
        if self.parent and view.parent and not comp:
            assert self.parent.name != view.parent.name, "unequal boxes with identical names %s, %s" % (
                self.parent.name, view.parent.name)

        return comp

    # Implement IRect by delegation.
    @property
    def left(self):
        return self.rect.left

    @property
    def top(self):
        return self.rect.top

    @property
    def right(self):
        return self.rect.right

    @property
    def bottom(self):
        return self.rect.bottom

    @property
    def width(self):
        return self.rect.width

    @property
    def height(self):
        return self.rect.height

    @property
    def center_x(self):
        return self.rect.center_x

    @property
    def center_y(self):
        return self.rect.center_x

    @property
    def size(self):
        return self.rect.size

    # Anchor and Edge convenience properties
    @property
    def left_anchor(self) -> Anchor:
        return Anchor(self, Attribute.LEFT)

    @property
    def left_edge(self) -> Edge:
        return Edge(self.left_anchor, (self.top, self.bottom))

    @property
    def top_anchor(self) -> Anchor:
        return Anchor(self, Attribute.TOP)

    @property
    def top_edge(self) -> Edge:
        return Edge(self.top_anchor, (self.left, self.right))

    @property
    def right_anchor(self) -> Anchor:
        return Anchor(self, Attribute.RIGHT)

    @property
    def right_edge(self) -> Edge:
        return Edge(self.right_anchor, (self.top, self.bottom))

    @property
    def bottom_anchor(self) -> Anchor:
        return Anchor(self, Attribute.BOTTOM)

    @property
    def bottom_edge(self) -> Edge:
        return Edge(self.bottom_anchor, (self.left, self.right))

    @property
    def center_x_anchor(self) -> Anchor:
        return Anchor(self, Attribute.CENTER_X)

    @property
    def center_x_edge(self) -> Edge:
        return Edge(self.center_x_anchor, (self.top, self.bottom))

    @property
    def center_y_anchor(self):
        return Anchor(self, Attribute.CENTER_Y)

    @property
    def center_y_edge(self) -> Edge:
        return Edge(self.center_y_anchor, (self.left, self.right))

    @property
    def width_anchor(self):
        return Anchor(self, Attribute.WIDTH)

    @property
    def height_anchor(self) -> Anchor:
        return Anchor(self, Attribute.HEIGHT)

    @property
    def anchor_labels(self):
        attrs = ["left", "right",
                 "top", "bottom",
                 "center_x", "center_y",
                 "width", "height"]
        return [f"{self.name}.{attr}" for attr in attrs]

    def get(self, name: str, default=None, include_self=False, deep=False) -> View[NT]:
        """
        Get the first child element with the given name, or return the default.
        :param name: the name of the view to get.
        :param default: the default to return if a view is not found.
        :param include_self: if true, then this element is itself included in the lookup.
        :param deep: if true, then the search recursive.
        """
        try:
            if include_self and self.name == name:
                return self
            if deep:
                return next(child for child in chain(*self.children) if child.name == name)
            else:
                it = (child for child in self.children if child.name == name)
                return next(it)
        except StopIteration:
            return default

    def get_anchor(self, anchor_id: AnchorID):
        [view_name, attr] = anchor_id

        view = self.get(view_name, include_self=True, deep=True)
        return getattr(view, f"{attr.value}_anchor")

    def __getitem__(self, name: str):
        """Get the immediate child with the given `name`, if it exists."""
        try:
            return next(child for child in self.children if child.name == name)
        except StopIteration:
            raise KeyError()

    def __iter__(self):
        yield self
        yield from chain(*map(iter, self.children))
        # noinspection PyTypeChecker
        # yield self
