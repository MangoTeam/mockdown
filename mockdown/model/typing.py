from __future__ import annotations

from abc import ABCMeta, abstractmethod
from dataclasses import dataclass, field
from itertools import chain
from typing import Tuple, List, Optional, Iterator, NamedTuple

from mockdown.model.attribute import Attribute


class Rect(NamedTuple):
    left: int
    right: int
    top: int
    bottom: int


@dataclass(frozen=True)
class AnchorID:
    view_name: str
    attribute: Attribute

    @classmethod
    def from_str(cls, s) -> Optional[AnchorID]:
        if s == 'None':
            return None
        v, a = s.split('.', 1)
        return cls(view_name=v, attribute=Attribute(a))

    def __str__(self):
        return f"{self.view_name}.{self.attribute.value}"

    def __iter__(self):
        return iter([self.view_name, self.attribute])


@dataclass(frozen=True)
class IAnchor(metaclass=ABCMeta):
    view: IView
    attribute: Attribute

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


@dataclass(frozen=True)
class IEdge(metaclass=ABCMeta):
    anchor: IAnchor
    interval: Tuple[int, int]

    @property
    @abstractmethod
    def view(self) -> IView: ...

    @property
    @abstractmethod
    def attribute(self) -> Attribute: ...

    @property
    @abstractmethod
    def position(self) -> int: ...


@dataclass(frozen=True)
class IView(metaclass=ABCMeta):
    name: str
    rect: Rect

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
    def center_x_edge(self) -> IEdge: ...

    @property
    @abstractmethod
    def center_y(self) -> int: ...

    @property
    @abstractmethod
    def center_y_anchor(self) -> IAnchor: ...

    @property
    @abstractmethod
    def center_y_edge(self) -> IEdge: ...

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
