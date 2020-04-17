""""
Rationale: View is a frozen (nearly immutable) class, but initializing a view
requires building both child and parent links.
"""
from __future__ import annotations

from abc import ABC, abstractmethod
from dataclasses import dataclass, field
from fractions import Fraction
from typing import Optional, Protocol, Sequence, Tuple, cast

from mockdown.model.primitives import IRect, QRect, RRect, ViewName, ZRect
from mockdown.model.typing import IView
from mockdown.model.view.view import View
from mockdown.typing import NT, Tuple4


# todo: only really from_dict is being used heavily here, though this \
#  could be really handy for testing... needs to be fixed up.

class IViewBuilder(Protocol[NT]):
    name: ViewName
    rect: Tuple[NT, NT, NT, NT]
    children: Sequence[IViewBuilder[NT]]
    parent: Optional[IViewBuilder[NT]]

    def build(self, parent_view: Optional[IView[NT]] = None) -> IView[NT]: ...


class _BaseViewBuilder(IViewBuilder[NT], ABC):
    @abstractmethod
    def _make_rect(self) -> IRect[NT]: ...

    def build(self, parent_view: Optional[IView[NT]] = None) -> IView[NT]:
        view = View(name=self.name,
                    rect=self._make_rect(),
                    parent=parent_view)

        # Note: Python's 'frozen' concept isn't *quite* immutable.
        # This is how we get around building a doubly-linked (up and down) frozen tree.
        # FrozenInstanceError is thrown in the dataclass' __setattr_, so we use __object__'s instead.

        child_views = [child.build(parent_view=view) for child in self.children]
        object.__setattr__(cast(object, view), 'children', child_views)

        return view


@dataclass(frozen=True)
class RViewBuilder(_BaseViewBuilder[float]):
    name: ViewName
    rect: Tuple4[float]
    children: Sequence[IViewBuilder[float]] = field(default_factory=list)
    parent: Optional[IViewBuilder[float]] = field(default=None)

    def _make_rect(self) -> RRect:
        return RRect(*self.rect)


@dataclass(frozen=True)
class QViewBuilder(_BaseViewBuilder[Fraction]):
    name: ViewName
    rect: Tuple4[Fraction]
    children: Sequence[IViewBuilder[Fraction]] = field(default_factory=list)
    parent: Optional[IViewBuilder[Fraction]] = field(default=None)

    def _make_rect(self) -> QRect:
        return QRect(*self.rect)


@dataclass(frozen=True)
class ZViewBuilder(_BaseViewBuilder[int]):
    name: ViewName
    rect: Tuple4[int]
    children: Sequence[IViewBuilder[int]] = field(default_factory=list)
    parent: Optional[IViewBuilder[int]] = field(default=None)

    def _make_rect(self) -> ZRect:
        return ZRect(*self.rect)
