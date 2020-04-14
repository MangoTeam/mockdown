""""
Rationale: View is a frozen (nearly immutable) class, but initializing a view
requires building both child and parent links.
"""
from __future__ import annotations

import json
from dataclasses import dataclass, field
from fractions import Fraction
from pathlib import Path
from typing import Tuple, List, Optional, Generic, cast

from .view import View
from .. import IView
from ..primitives import ZRect, QRect, RRect, IRect, ViewName
from ...typing import NT

# todo: only really from_dict is being used heavily here, though this \
#  could be really handy for testing... needs to be fixed up.

@dataclass
class ViewBuilder(Generic[NT]):
    name: ViewName
    rect: Tuple[NT, NT, NT, NT]
    children: List[ViewBuilder] = field(default_factory=list)
    parent: Optional[ViewBuilder] = field(default=None)

    # TODO: Add this magic back for testing?
    # def __post_init__(self):
    #     def normalize_children(child_or_args: Union[ViewBuilder, Tuple]):
    #         if isinstance(child_or_args, list) or isinstance(child_or_args, tuple):
    #             return ViewBuilder(*child_or_args)
    #         elif isinstance(child_or_args, dict):
    #             return ViewBuilder(**child_or_args)
    #         else:
    #             return child_or_args
    #
    #     self.children = list(map(normalize_children, self.children))
    #
    #     for child in self.children:
    #         child.parent = self

    def add_child(self, child: ViewBuilder):
        child.parent = self
        self.children += [child]

    # todo: This is some janky dynamic type stuff
    def make_rect(self):
        if isinstance(self.rect[0], int):
            return ZRect(*cast(Tuple[int, int, int, int], self.rect))
        elif isinstance(self.rect[0], float):
            return RRect(*cast(Tuple[float, float, float, float], self.rect))
        elif isinstance(self.rect[0], Fraction):
            return QRect(*cast(Tuple[Fraction, Fraction, Fraction, Fraction], self.rect))

    def to_view(self, parent_view=None) -> IView[NT]:
        assert self.name, "View must have a name."
        assert self.rect, "View must have a rect."

        view: IView[NT] = View(name=self.name,
                               rect=self.make_rect(),
                               parent=parent_view)

        # Note: Python's 'frozen' concept isn't *quite* immutable.
        # This is how we get around building a doubly-linked (up and down) frozen tree.
        # FrozenInstanceError is thrown in the dataclass' __setattr_, so we use __object__'s instead.

        child_views = [child.to_view(parent_view=view) for child in self.children]
        object.__setattr__(cast(object, view), 'children', child_views)

        return view

    @classmethod
    def from_dict(cls, d: dict) -> ViewBuilder:
        return cls(**d)

    @classmethod
    def from_file(cls, p: Path):
        with p.open('r') as f:
            return cls.from_dict(json.load(f))
