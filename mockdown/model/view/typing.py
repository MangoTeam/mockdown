from __future__ import annotations

from abc import abstractmethod
from typing import Protocol, List, Optional, Sequence

from .. import IEdge, IAnchor
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
