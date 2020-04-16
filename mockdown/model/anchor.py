from __future__ import annotations

import re
from dataclasses import dataclass
from typing import NamedTuple, Optional, Tuple, cast

from .primitives import Attribute, ViewName
from .typing import IAnchor, IAnchorID, IEdge
from .view import IView
from ..typing import NT


@dataclass(frozen=True, eq=True)
class AnchorID(IAnchorID):
    view_name: ViewName
    attribute: Attribute

    @classmethod
    def from_str(cls, s: str) -> Optional[AnchorID]:
        if s == 'None':
            return None

        if (m := re.match(r'(\w+)\.(\w+)', s)) is None:
            raise Exception(f"{s} is not a valid anchor ID string.")

        v, a = m.groups()
        return cls(view_name=v, attribute=Attribute(a))

    def __str__(self) -> str:
        return f"{self.view_name}.{self.attribute.value}"


@dataclass(frozen=True)
class Anchor(IAnchor[NT]):
    view: IView[NT]
    attribute: Attribute

    @property
    def id(self) -> IAnchorID:
        return AnchorID(self.view.name, self.attribute)

    @property
    def name(self) -> ViewName:
        return f"{self.view.name}.{self.attribute}"

    @property
    def value(self) -> NT:
        return cast(NT, getattr(self.view, self.attribute.value))

    @property
    def edge(self) -> IEdge[NT]:
        return cast(IEdge[NT], getattr(self.view, f"{self.attribute.value}_edge"))

    def __repr__(self) -> str:
        return f"{self.name} @ {self.value}"
