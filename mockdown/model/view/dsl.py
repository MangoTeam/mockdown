from __future__ import annotations

from abc import abstractmethod
from typing import List, Optional, Protocol, Sequence, Tuple, Type, Union

from .typing import IView
from .view import View
from ..primitives import IRect, ViewName
from ...typing import NT

RectParams = Tuple[NT, NT, NT, NT]

BuilderParams = Tuple[ViewName,
                      Union[RectParams, IRect[NT]],
                      Sequence[Union['BuilderParams', 'IViewBuilder[NT]']]]


@runtime_checkable
class IViewBuilder(Protocol[NT]):
    name: ViewName
    rect: IRect[NT]
    children: List[IViewBuilder[NT]]

    def __init__(self, *args: BuilderParams):
        (name, rect, children) = args
        self.name = name
        self.rect = type(self).normalize_rect(rect)
        self.children = type(self).normalize_children(children)

    @classmethod
    @abstractmethod
    def numeric_type(cls) -> Type[NT]:
        ...

    @classmethod
    @abstractmethod
    def make_rect(cls) -> IRect[NT]:
        ...

    @classmethod
    def normalize_rect(cls, rect: Union[IRect[NT], RectParams]) -> IRect[NT]:
        if isinstance(rect, IRect):
            return rect
        elif isinstance(rect, Tuple):
            return cls.make_rect(*rect)
        else:
            unreachable(type(rect))

    @classmethod
    def normalize_children(cls, children: Sequence[Union[BuilderParams, IViewBuilder[NT]]]) -> Sequence[
        IViewBuilder[NT]]:
        return []

    def build(self, parent: Optional[IView[NT]] = None) -> IView[NT]:
        children = [child.build(parent=parent) for child in self.children]

        return View(name=self.name,
                    rect=self.rect,
                    children=children,
                    parent=parent)
