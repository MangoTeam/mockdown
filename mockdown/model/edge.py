from dataclasses import dataclass

from mockdown.model.attribute import Attribute
from mockdown.model.typing import IEdge, IView


@dataclass(frozen=True)
class Edge(IEdge):
    @property
    def view(self) -> IView:
        return self.anchor.view

    @property
    def attribute(self) -> Attribute:
        return self.anchor.attribute

    @property
    def position(self) -> int:
        return self.anchor.value

    def __post_init__(self):
        assert self.interval[0] <= self.interval[1]

    def __repr__(self):
        return f"{self.view.name}.{self.attribute.value} {self.interval} @ {self.position}"
