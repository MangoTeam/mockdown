from dataclasses import dataclass
from typing import Tuple

from mockdown.model.primitives import Attribute
from mockdown.model.types import IAnchor, IEdge, IView
from mockdown.types import NT


@dataclass(frozen=True)
class Edge(IEdge[NT]):
    anchor: IAnchor[NT]
    interval: Tuple[NT, NT]

    @property
    def view(self) -> IView[NT]:
        return self.anchor.view

    @property
    def attribute(self) -> Attribute:
        return self.anchor.attribute

    @property
    def position(self) -> NT:
        return self.anchor.value

    def __post_init__(self) -> None:
        assert self.interval[0] <= self.interval[1]

    def __repr__(self) -> str:
        return f"{self.view.name}.{self.attribute.value} {self.interval} @ {self.position}"
