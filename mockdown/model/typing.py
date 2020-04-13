from __future__ import annotations

from abc import abstractmethod
from typing import Protocol, Tuple

from .primitives import Attribute, ViewName
from .view import IView
from ..typing import NT, NT_Co


class IAnchorID(Protocol):
    view_name: ViewName
    attribute: Attribute


class IAnchor(Protocol[NT_Co]):
    view: IView[NT_Co]
    attribute: Attribute

    @property
    @abstractmethod
    def id(self) -> IAnchorID: ...

    @property
    @abstractmethod
    def name(self) -> ViewName: ...

    @property
    @abstractmethod
    def value(self) -> NT_Co: ...

    @property
    @abstractmethod
    def edge(self) -> IEdge: ...


class IEdge(Protocol[NT]):
    anchor: IAnchor
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
