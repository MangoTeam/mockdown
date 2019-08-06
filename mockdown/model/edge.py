from dataclasses import dataclass

from .typing import IEdge


@dataclass(frozen=True)
class Edge(IEdge):
    @property
    def view(self):
        return self.anchor.view

    @property
    def attribute(self):
        return self.anchor.attribute

    @property
    def position(self):
        return self.anchor.value

    def __post_init__(self):
        assert self.interval[0] <= self.interval[1]

    def __repr__(self):
        return f"{self.view.name}.{self.attribute} {self.interval} @ {self.position}"
