""""
Rationale: View is a frozen (nearly immutable) class, but initializing a view
requires building both child and parent links.
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Optional, Protocol, Sequence, cast, Type, Tuple, List

import sympy as sym

from mockdown.model.primitives import IRect, ViewName, Rect
from mockdown.model.typing import IView
from mockdown.model.view.typing import NumberConvertible as NumConv
from mockdown.model.view.view import View
from mockdown.typing import NT


# This is a set of types that sympy.Number's constructor will accept.

class IViewBuilder(Protocol):
    name: ViewName
    rect: Tuple[NumConv, NumConv, NumConv, NumConv]
    children: Sequence[IViewBuilder]
    parent: Optional[IViewBuilder]

    def build(self, number_type: Type[NT], parent_view: Optional[IView[NT]] = None) -> IView[
        NT]: ...


@dataclass
class ViewBuilder(IViewBuilder):
    name: ViewName
    rect: Tuple[NumConv, NumConv, NumConv, NumConv]
    children: Sequence[IViewBuilder] = field(default_factory=list)
    parent: Optional[IViewBuilder] = field(default=None)

    # Note: NT is _not_ bound at the class level, the universal quantifier over NT is on the method!
    # This method is dependently typed, and is parametrized by the numeric type (as a value).
    def build(self, number_type: Type[NT], parent_view: Optional[IView[NT]] = None) -> IView[NT]:
        view: IView[NT] = View(name=self.name,
                               rect=self._make_rect(number_type),
                               parent=parent_view)

        child_views = [child.build(number_type=number_type, parent_view=view) for child in self.children]
        object.__setattr__(cast(object, view), 'children', child_views)

        return view

    def _make_rect(self, number_type: Type[NT]) -> IRect[NT]:
        args: List[NT] = [number_type(v) for v in self.rect]
        return Rect(*args)
