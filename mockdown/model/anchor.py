from __future__ import annotations

from dataclasses import dataclass
from typing import Optional

import z3

from .typing import IAnchor, IAnchorID, IEdge
from . import IView
from .primitives import Attribute, ViewName


@dataclass(frozen=True)
class AnchorID(IAnchorID):
    view_name: ViewName
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

    def to_z3_var(self, idx: int, linearize: bool):
        if linearize:
            return z3.Int(str(self) + "_" + str(idx))
        else:
            return z3.Real(str(self) + "_" + str(idx))


@dataclass(frozen=True)
class Anchor(IAnchor):
    view: IView
    attribute: Attribute

    @property
    def id(self) -> AnchorID:
        return AnchorID(self.view.name, self.attribute)

    @property
    def name(self) -> ViewName:
        return f"{self.view.name}.{self.attribute}"

    @property
    def value(self) -> int:
        return getattr(self.view, self.attribute.value)

    @property
    def edge(self) -> IEdge:
        return getattr(self.view, f"{self.attribute.value}_edge")

    def __repr__(self) -> str:
        return f"{self.name} @ {self.value}"
