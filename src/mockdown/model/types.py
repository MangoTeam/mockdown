from __future__ import annotations

from abc import abstractmethod
from typing import Iterator, Optional, Protocol, Sequence, Tuple, Any, List, Dict

from mockdown.model.primitives import Attribute, IRect, ViewName
from mockdown.types import NT


class IAnchorID(Protocol):
    view_name: ViewName
    attribute: Attribute


class IAnchor(Protocol[NT]):
    view: IView[NT]
    attribute: Attribute

    @property
    @abstractmethod
    def id(self) -> IAnchorID: ...

    @property
    @abstractmethod
    def name(self) -> ViewName: ...

    @property
    @abstractmethod
    def value(self) -> NT: ...

    @property
    @abstractmethod
    def edge(self) -> IEdge[NT]: ...


class IEdge(Protocol[NT]):
    anchor: IAnchor[NT]
    interval: Tuple[NT, NT]

    @property
    @abstractmethod
    def view(self) -> IView[NT]: ...

    @property
    @abstractmethod
    def attribute(self) -> Attribute: ...

    @property
    @abstractmethod
    def position(self) -> NT: ...


class IView(Protocol[NT]):
    name: ViewName
    rect: IRect[NT]
    children: Sequence[IView[NT]]
    parent: Optional[IView[NT]]

    # Implement IRect by delegation.
    # IRect isn't explicitly implemented because mypy is dumb.
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
        return self.rect.center_y

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
    def anchors(self) -> List[IAnchor[NT]]: ...

    @property
    @abstractmethod
    def names(self) -> Iterator[str]: ...
    

    @property
    @abstractmethod
    def center_y_anchor(self) -> IAnchor[NT]: ...

    @property
    @abstractmethod
    def x_anchors(self) -> List[IAnchor[NT]]: ...

    @property
    @abstractmethod
    def y_anchors(self) -> List[IAnchor[NT]]: ...

    def find_view(self, name: ViewName, include_self: bool = False, deep: bool = False) -> Optional[IView[NT]]:
        ...

    def find_anchor(self, anchor_id: IAnchorID) -> Optional[IAnchor[NT]]:
        ...

    def is_parent_of(self, view: IView[NT]) -> bool:
        ...

    def is_parent_of_name(self, vs: ViewName) -> bool:
        ...

    def is_child_of(self, view: IView[NT]) -> bool:
        ...

    def is_sibling_of(self, view: IView[NT]) -> bool:
        ...

    def is_isomorphic(self, view: IView[NT], include_names: bool = True) -> bool:
        ...

    def __eq__(self, other: object) -> bool: ...

    def __iter__(self) -> Iterator[IView[NT]]: ...

    def to_dict(self) -> Dict[str, Any]: ...
