from __future__ import annotations

from abc import abstractmethod
from dataclasses import dataclass
from typing import Protocol

from ...typing import NT

class IRect(Protocol[NT]):
    left: NT
    top: NT
    right: NT
    bottom: NT

    @property
    @abstractmethod
    def width(self) -> NT: ...

    @property
    @abstractmethod
    def height(self) -> NT: ...

    @property
    @abstractmethod
    def center_x(self) -> NT: ...

    @property
    @abstractmethod
    def center_y(self) -> NT: ...


@dataclass(eq=True)
class Rect(IRect[NT]):
    """
    Implementation of IRect for sympy's Number types.
    """
    left: NT
    top: NT
    right: NT
    bottom: NT

    @property
    def width(self) -> NT:
        return self.right - self.left

    @property
    def height(self) -> NT:
        return self.bottom - self.top

    @property
    def center_x(self) -> NT:
        return (self.left + self.right) / 2

    @property
    def center_y(self) -> NT:
        return (self.top + self.bottom) / 2
