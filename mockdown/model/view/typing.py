from __future__ import annotations

from abc import abstractmethod
from itertools import chain
from typing import Protocol, Optional, Sequence

from .. import IEdge, IAnchor, IAnchorID
from ..primitives import ViewName, IRect
from ...typing import NT


class IView(Protocol[NT], IRect[NT]):
    name: ViewName
    rect: IRect[NT]
    children: Sequence[IView]
    parent: Optional[IView]

    def get(self, name: str, default=None, include_self=False, deep=False) -> IView[NT]:
        ...

    def is_parent_of(self, view) -> bool:
        ...

    def is_parent_of_name(self, vs: ViewName) -> bool:
        ...

    def is_child_of(self, view) -> bool:
        ...

    def is_sibling_of(self, view) -> bool:
        ...

    # Implement IRect by delegation.
    @property
    def left(self) -> NT:
        return self.rect.left

    @property
    def top(self) -> NT:
        return self.rect.top

    @property
    def right(self) -> NT:
        return self.rect.right

    @property
    def bottom(self) -> NT:
        return self.rect.bottom

    @property
    def width(self) -> NT:
        return self.rect.width

    @property
    def height(self) -> NT:
        return self.rect.height

    @property
    def center_x(self) -> NT:
        return self.rect.center_x

    @property
    def center_y(self) -> NT:
        return self.rect.center_x

    @property
    def size(self):
        return self.rect.size

    @property
    @abstractmethod
    def left_edge(self) -> IEdge[NT]: ...

    @property
    @abstractmethod
    def top_edge(self) -> IEdge[NT]: ...

    @property
    @abstractmethod
    def right_edge(self) -> IEdge[NT]: ...

    @property
    @abstractmethod
    def bottom_edge(self) -> IEdge[NT]: ...

    @property
    @abstractmethod
    def left_anchor(self) -> IAnchor[NT]: ...

    @property
    @abstractmethod
    def top_anchor(self) -> IAnchor[NT]: ...

    @property
    @abstractmethod
    def right_anchor(self) -> IAnchor[NT]: ...

    @property
    @abstractmethod
    def bottom_anchor(self) -> IAnchor[NT]: ...

    @property
    @abstractmethod
    def width_anchor(self) -> IAnchor[NT]: ...

    @property
    @abstractmethod
    def height_anchor(self) -> IAnchor[NT]: ...

    @property
    @abstractmethod
    def center_x_anchor(self) -> IAnchor[NT]: ...

    @property
    @abstractmethod
    def center_y_anchor(self) -> IAnchor[NT]: ...

    def get_anchor(self, anchor_id: IAnchorID) -> IAnchor[NT]: ...

    def __iter__(self):
        yield self
        yield from chain(*map(iter, self.children))
