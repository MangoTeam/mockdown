""""
Rationale: View is a frozen (nearly immutable) class, but initializing a view
requires building both child and parent links.
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Optional, Protocol, Sequence, cast

from sympy import Number  # type: ignore

from mockdown.model.primitives import IRect, ViewName, Rect
from mockdown.model.typing import IView
from mockdown.model.view.typing import NumberConvertible, NumberFactory
from mockdown.model.view.view import View
from mockdown.typing import NT, Tuple4

# This is a set of types that sympy.Number's constructor will accept.


class IViewBuilder(Protocol[NT]):
    name: ViewName
    rect: Tuple4[NumberConvertible]
    children: Sequence[IViewBuilder[NT]]
    parent: Optional[IViewBuilder[NT]]

    def build(self, parent_view: Optional[IView[NT]] = None, number_factory: NumberFactory = Number) -> IView[NT]: ...


@dataclass
class ViewBuilder(IViewBuilder[Number]):
    name: ViewName
    rect: Tuple4[NumberConvertible]
    children: Sequence[IViewBuilder[Number]] = field(default_factory=list)
    parent: Optional[IViewBuilder[Number]] = field(default=None)

    def build(self, parent_view: Optional[IView[NT]] = None, number_factory: NumberFactory = Number) -> IView[NT]:
        view = View(name=self.name,
                    rect=self._make_rect(number_factory),
                    parent=parent_view)

        child_views = [child.build(parent_view=view) for child in self.children]
        object.__setattr__(cast(object, view), 'children', child_views)

        return view

    def _make_rect(self, number_factory: NumberFactory) -> IRect[NT]:
        args = map(number_factory, self.rect)
        return Rect(*args)
