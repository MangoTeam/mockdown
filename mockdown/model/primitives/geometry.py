from __future__ import annotations

from abc import abstractmethod
from dataclasses import dataclass
from fractions import Fraction
from typing import Protocol, TypeVar

from ...typing import NT


class IRect(Protocol[NT]):
    @property
    @abstractmethod
    def left(self) -> NT: ...

    @property
    @abstractmethod
    def top(self) -> NT: ...

    @property
    @abstractmethod
    def right(self) -> NT: ...

    @property
    @abstractmethod
    def bottom(self) -> NT: ...

    @property
    @abstractmethod
    def width(self) -> NT:
        return self.right - self.left

    @property
    @abstractmethod
    def height(self) -> NT:
        return self.bottom - self.top

    @property
    @abstractmethod
    def center_x(self) -> NT: ...

    @property
    @abstractmethod
    def center_y(self) -> NT: ...

    @property
    @abstractmethod
    def size(self) -> ISize[NT]: ...


@dataclass(frozen=True)
class QRect(IRect[Fraction]):
    left: Fraction
    top: Fraction
    right: Fraction
    bottom: Fraction

    @property
    def width(self) -> Fraction:
        return self.right - self.left

    @property
    def height(self) -> Fraction:
        return self.bottom - self.top

    @property
    def size(self) -> ISize[Fraction]:
        return QSize(self.width, self.height)

    @property
    def center_x(self):
        return (self.left + self.right) / 2

    @property
    def center_y(self) -> Fraction:
        return (self.top + self.bottom) / 2


@dataclass(frozen=True)
class RRect(IRect[float]):
    left: float
    top: float
    right: float
    bottom: float

    @property
    def width(self) -> float:
        return self.right - self.left

    @property
    def height(self) -> float:
        return self.bottom - self.top

    @property
    def size(self) -> ISize[float]:
        return RSize(self.width, self.height)

    @property
    def center_x(self):
        return (self.left + self.right) / 2

    @property
    def center_y(self) -> float:
        return (self.top + self.bottom) / 2


@dataclass(frozen=True)
class ZRect(IRect[int]):
    left: int
    top: int
    right: int
    bottom: int

    @property
    def width(self) -> int:
        return self.right - self.left

    @property
    def height(self) -> int:
        return self.bottom - self.top

    @property
    def size(self) -> ISize[int]:
        return ZSize(self.width, self.height)

    @property
    def center_x(self):
        return (self.left + self.right) // 2

    @property
    def center_y(self) -> int:
        return (self.top + self.bottom) // 2


class ISize(Protocol[NT]):
    width: NT
    height: NT


@dataclass(frozen=True)
class ZSize(ISize[int]):
    width: int
    height: int


@dataclass(frozen=True)
class QSize(ISize[Fraction]):
    width: Fraction
    height: Fraction


@dataclass(frozen=True)
class RSize(ISize[float]):
    width: float
    height: float
