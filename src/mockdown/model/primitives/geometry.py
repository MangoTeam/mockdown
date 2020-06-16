from __future__ import annotations

from abc import abstractmethod
from dataclasses import dataclass
from fractions import Fraction
from typing import Protocol, cast

from sympy import Number, Float  # type: ignore

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
class Rect(IRect[Number]):
    """
    Implementation of IRect for sympy's Number types.
    """
    left: Number
    top: Number
    right: Number
    bottom: Number

    @property
    def width(self) -> Number:
        return self.right - self.left

    @property
    def height(self) -> Number:
        return self.bottom - self.top

    @property
    def center_x(self) -> Number:
        return (self.left + self.right) / 2

    @property
    def center_y(self) -> Number:
        return (self.top + self.bottom) / 2
