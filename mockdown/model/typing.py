from __future__ import annotations

from abc import ABCMeta, abstractmethod
from dataclasses import dataclass, field
from typing import Tuple, List, Optional, Iterator

AnchorID = Tuple[str, str]


@dataclass
class IAnchor(metaclass=ABCMeta):
    view: IView
    attribute: str

    @property
    @abstractmethod
    def identifier(self) -> AnchorID: ...

    @property
    @abstractmethod
    def name(self) -> str: ...

    @property
    @abstractmethod
    def value(self) -> int: ...

    @property
    @abstractmethod
    def edge(self) -> IEdge: ...


@dataclass
class IEdge(metaclass=ABCMeta):
    anchor: IAnchor
    interval: Tuple[int, int]

    @property
    @abstractmethod
    def view(self) -> IView: ...

    @property
    @abstractmethod
    def attribute(self) -> str: ...

    @property
    @abstractmethod
    def position(self) -> int: ...


@dataclass
class IView(metaclass=ABCMeta):
    name: str
    rect: Tuple[int, int, int, int]

    children: List[IView] = field(default_factory=list)
    parent: Optional[IView] = field(default=None)

    @abstractmethod
    def is_parent_of(self, view: IView) -> bool: ...

    @abstractmethod
    def is_child_of(self, view: IView) -> bool: ...

    @abstractmethod
    def is_sibling_of(self, view: IView) -> bool: ...

    @property
    @abstractmethod
    def left(self) -> int: ...

    @property
    @abstractmethod
    def left_anchor(self) -> IAnchor: ...

    @property
    @abstractmethod
    def left_edge(self) -> IEdge: ...

    @property
    @abstractmethod
    def top(self) -> int: ...

    @property
    @abstractmethod
    def top_anchor(self) -> IAnchor: ...

    @property
    @abstractmethod
    def top_edge(self) -> IEdge: ...

    @property
    @abstractmethod
    def right(self) -> int: ...

    @property
    @abstractmethod
    def right_anchor(self) -> IAnchor: ...

    @property
    @abstractmethod
    def right_edge(self) -> IEdge: ...

    @property
    @abstractmethod
    def bottom(self) -> int: ...

    @property
    @abstractmethod
    def bottom_anchor(self) -> IAnchor: ...

    @property
    @abstractmethod
    def bottom_edge(self) -> IEdge: ...

    @property
    @abstractmethod
    def center_x(self) -> int: ...

    @property
    @abstractmethod
    def center_x_anchor(self) -> IAnchor: ...

    @property
    @abstractmethod
    def center_y(self) -> int: ...

    @property
    @abstractmethod
    def center_y_anchor(self) -> IAnchor: ...

    @property
    @abstractmethod
    def width(self) -> int: ...

    @property
    @abstractmethod
    def width_anchor(self) -> IAnchor: ...

    @property
    @abstractmethod
    def height(self) -> int: ...

    @property
    @abstractmethod
    def height_anchor(self) -> IAnchor: ...

    @property
    @abstractmethod
    def anchor_labels(self) -> List[str]: ...

    @abstractmethod
    def get(self, name: str, default=None, include_self=False, deep=False) -> IView: ...

    @abstractmethod
    def get_anchor(self, anchor_id: AnchorID) -> IAnchor: ...

    @abstractmethod
    def __getitem__(self, item: str): ...

    @abstractmethod
    def __iter__(self) -> Iterator[IView]: ...
