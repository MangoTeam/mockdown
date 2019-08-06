""""
Rationale: View is a frozen (nearly immutable) class, but initializing a view
requires building both child and parent links.
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Tuple, List, Optional

from mockdown.model import IView
from mockdown.model.view.view import View


@dataclass
class ViewBuilder:
    name: str
    rect: Tuple[int, int, int, int]
    children: List[ViewBuilder] = field(default_factory=list)
    parent: Optional[ViewBuilder] = field(default=None)

    def __post_init__(self):
        for child in self.children:
            child.parent = self

    def add_child(self, child: ViewBuilder):
        child.parent = self
        self.children += child

    def to_view(self) -> IView:
        assert self.name, "View must have a name."
        assert self.rect, "View must have a rect."

        view = View(name=self.name,
                    rect=self.rect,
                    children=[child.to_view() for child in self.children],
                    parent=self.parent)

        return view
