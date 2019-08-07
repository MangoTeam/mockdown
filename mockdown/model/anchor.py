from __future__ import annotations

from dataclasses import dataclass

from mockdown.model.typing import IAnchor, AnchorID, IEdge


@dataclass(frozen=True)
class Anchor(IAnchor):
    @property
    def identifier(self) -> AnchorID:
        return AnchorID(self.view.name, self.attribute)

    @property
    def name(self) -> str:
        return f"{self.view.name}.{self.attribute}"

    @property
    def value(self) -> int:
        return getattr(self.view, self.attribute.value)

    @property
    def edge(self) -> IEdge:
        return getattr(self.view, f"{self.attribute.value}_edge")

    def __repr__(self) -> str:
        return f"{self.name} @ {self.value}"
