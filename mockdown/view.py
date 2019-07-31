from dataclasses import dataclass, field
from itertools import chain
from typing import List, Tuple


@dataclass
class Anchor:
    view: 'View'
    attribute: str

    @property
    def name(self):
        return f"{self.view.name}.{self.attribute}"

    @property
    def value(self):
        return getattr(self.view, self.attribute)

    @property
    def edge(self) -> 'Edge':
        return getattr(self.view, f"{self.attribute}_edge")

    def __repr__(self):
        return f"{self.name} @ {self.value}"


@dataclass
class Edge:
    anchor: Anchor
    interval: Tuple[int, int]

    @property
    def view(self) -> 'View':
        return self.anchor.view

    @property
    def attribute(self) -> str:
        return self.anchor.attribute

    @property
    def position(self) -> int:
        return self.anchor.value

    def __post_init__(self):
        assert self.interval[0] <= self.interval[1]

    def __repr__(self):
        return f"{self.view.name}.{self.attribute} {self.interval} @ {self.position}"


@dataclass
class View:
    name: str
    rect: Tuple[int, int, int, int]
    children: List['View'] = field(default_factory=list)

    @property
    def left(self) -> int:
        return self.rect[0]

    @property
    def left_anchor(self) -> Anchor:
        return Anchor(self, 'left')

    @property
    def left_edge(self) -> Edge:
        return Edge(self.left_anchor, (self.top, self.bottom))

    @property
    def top(self) -> int:
        return self.rect[1]

    @property
    def top_anchor(self) -> Anchor:
        return Anchor(self, 'top')

    @property
    def top_edge(self) -> Edge:
        return Edge(self.top_anchor, (self.left, self.right))

    @property
    def right(self) -> int:
        return self.rect[2]

    @property
    def right_anchor(self) -> Anchor:
        return Anchor(self, 'right')

    @property
    def right_edge(self) -> Edge:
        return Edge(self.right_anchor, (self.top, self.bottom))

    @property
    def bottom(self) -> int:
        return self.rect[3]

    @property
    def bottom_anchor(self) -> Anchor:
        return Anchor(self, 'bottom')

    @property
    def bottom_edge(self) -> Edge:
        return Edge(self.bottom_anchor, (self.left, self.right))

    @property
    def center_x(self):
        return (self.left + self.right) / 2

    @property
    def center_x_anchor(self) -> Anchor:
        return Anchor(self, 'center_x')

    @property
    def center_y(self):
        return (self.top + self.bottom) / 2

    @property
    def center_y_anchor(self) -> Anchor:
        return Anchor(self, 'center_y')

    @property
    def width(self):
        return self.right - self.left

    @property
    def width_anchor(self) -> Anchor:
        return Anchor(self, 'width')

    @property
    def height(self):
        return self.bottom - self.top

    @property
    def height_anchor(self) -> Anchor:
        return Anchor(self, 'height')

    @property
    def anchor_labels(self):
        attrs = ["left", "right",
                 "top", "bottom",
                 "center_x", "center_y",
                 "width", "height"]
        return [f"{self.name}.{attr}" for attr in attrs]

    def get(self, name: str, default=None, include_self=False, deep=False):
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

    def __getitem__(self, name: str):
        """Get the immediate child with the given `name`, if it exists."""
        try:
            return next(child for child in self.children if child.name == name)
        except StopIteration:
            raise KeyError()

    def __iter__(self):
        yield self
        # noinspection PyTypeChecker
        yield from chain(*map(iter, self.children))
