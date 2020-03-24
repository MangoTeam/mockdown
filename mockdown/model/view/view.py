from dataclasses import dataclass
from itertools import chain

from mockdown.model.anchor import Anchor
from mockdown.model.attribute import Attribute
from mockdown.model.edge import Edge
from mockdown.model.typing import IAnchor, IEdge, IView, AnchorID


@dataclass(frozen=True)
class View(IView):
    def is_parent_of(self, view) -> bool:
        return view.parent == self

    def is_parent_of_name(self, vs: str) -> bool:
        return len([x for x in self.children if x.name == vs]) == 1

    def is_child_of(self, view) -> bool:
        return self.parent == view

    def is_sibling_of(self, view) -> bool:
        comp = self.parent == view.parent
        if self.parent and view.parent and not comp: 
            assert self.parent.name != view.parent.name, "unequal boxes with identical names %s, %s" % (self.parent.name, view.parent.name)

        return comp

    @property
    def left(self) -> int:
        return self.rect[0]

    @property
    def left_anchor(self) -> IAnchor:
        return Anchor(self, Attribute.LEFT)

    @property
    def left_edge(self) -> IEdge:
        return Edge(self.left_anchor, (self.top, self.bottom))

    @property
    def top(self) -> int:
        return self.rect[1]

    @property
    def top_anchor(self) -> IAnchor:
        return Anchor(self, Attribute.TOP)

    @property
    def top_edge(self) -> IEdge:
        return Edge(self.top_anchor, (self.left, self.right))

    @property
    def right(self) -> int:
        return self.rect[2]

    @property
    def right_anchor(self) -> IAnchor:
        return Anchor(self, Attribute.RIGHT)

    @property
    def right_edge(self) -> IEdge:
        return Edge(self.right_anchor, (self.top, self.bottom))

    @property
    def bottom(self) -> int:
        return self.rect[3]

    @property
    def bottom_anchor(self) -> IAnchor:
        return Anchor(self, Attribute.BOTTOM)

    @property
    def bottom_edge(self) -> IEdge:
        return Edge(self.bottom_anchor, (self.left, self.right))

    @property
    def center_x(self):
        return (self.left + self.right) // 2

    @property
    def center_x_anchor(self) -> IAnchor:
        return Anchor(self, Attribute.CENTER_X)

    @property
    def center_x_edge(self) -> IEdge:
        return Edge(self.center_x_anchor, (self.top, self.bottom))

    @property
    def center_y(self) -> int:
        return (self.top + self.bottom) // 2

    @property
    def center_y_anchor(self):
        return Anchor(self, Attribute.CENTER_Y)

    @property
    def center_y_edge(self) -> IEdge:
        return Edge(self.center_y_anchor, (self.left, self.right))

    @property
    def width(self):
        return self.right - self.left

    @property
    def width_anchor(self):
        return Anchor(self, Attribute.WIDTH)

    @property
    def height(self):
        return self.bottom - self.top

    @property
    def height_anchor(self) -> IAnchor:
        return Anchor(self, Attribute.HEIGHT)

    @property
    def anchor_labels(self):
        attrs = ["left", "right",
                 "top", "bottom",
                 "center_x", "center_y",
                 "width", "height"]
        return [f"{self.name}.{attr}" for attr in attrs]

    def get(self, name: str, default=None, include_self=False, deep=False) -> IView:
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
                return next(child for child in self.children if child.name == name)
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
