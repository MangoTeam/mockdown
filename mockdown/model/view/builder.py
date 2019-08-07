""""
Rationale: View is a frozen (nearly immutable) class, but initializing a view
requires building both child and parent links.
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Tuple, List, Optional, Union

from mockdown.model import IView
from mockdown.model.view.view import View


@dataclass
class ViewBuilder:
    name: str
    rect: Tuple[int, int, int, int]
    children: List[Union[ViewBuilder, Tuple]] = field(default_factory=list)
    parent: Optional[ViewBuilder] = field(default=None)

    def __post_init__(self):
        def normalize_children(child_or_args: Union[ViewBuilder, Tuple]):
            if isinstance(child_or_args, tuple):
                return ViewBuilder(*child_or_args)
            else:
                return child_or_args

        self.children = list(map(normalize_children, self.children))

        for child in self.children:
            child.parent = self

    def add_child(self, child: ViewBuilder):
        child.parent = self
        self.children += child

    def to_view(self, parent_view=None) -> IView:
        assert self.name, "View must have a name."
        assert self.rect, "View must have a rect."

        view = View(name=self.name,
                    rect=self.rect,
                    parent=parent_view)

        # Note: Python's 'frozen' concept isn't *quite* immutable.
        # This is how we get around building a doubly-linked (up and down) frozen tree.
        # FrozenInstanceError is thrown in the dataclass' __setattr_, so we use __object__'s instead.

        child_views = [child.to_view(parent_view=view) for child in self.children]
        object.__setattr__(view, 'children', child_views)

        return view
