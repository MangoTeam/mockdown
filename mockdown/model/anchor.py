from __future__ import annotations

from dataclasses import dataclass

from .typing import IAnchor


@dataclass(frozen=True)
class Anchor(IAnchor):
    @property
    def identifier(self):
        return self.view.name, self.attribute

    @property
    def name(self):
        return f"{self.view.name}.{self.attribute}"

    @property
    def value(self):
        return getattr(self.view, self.attribute)

    @property
    def edge(self):
        return getattr(self.view, f"{self.attribute}_edge")

    def __repr__(self):
        return f"{self.name} @ {self.value}"
