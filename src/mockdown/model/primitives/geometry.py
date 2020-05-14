from __future__ import annotations

from abc import abstractmethod
from dataclasses import dataclass
from fractions import Fraction
from typing import Protocol, cast

from ...typing import NT, NT_co

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

    @property
    @abstractmethod
    def size(self) -> ISize[NT]: ...


@dataclass(eq=True)
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
    def center_x(self) -> float:
        return (self.left + self.right) / 2

    @property
    def center_y(self) -> float:
        return (self.top + self.bottom) / 2


@dataclass(eq=True)
class QRect(IRect[Fraction]):
    left: Fraction
    top: Fraction
    right: Fraction
    bottom: Fraction

    r"""
    Note: mypy has incomplete stubs for Fraction, so __sub__: (Any, Any) -> Any erroneously.
    We just have to force it with a cast. ¯\_(ツ)_/¯
    """

    @property
    def width(self) -> Fraction:
        return cast(Fraction, self.right - self.left)

    @property
    def height(self) -> Fraction:
        return cast(Fraction, self.bottom - self.top)

    @property
    def size(self) -> ISize[Fraction]:
        return QSize(self.width, self.height)

    @property
    def center_x(self) -> Fraction:
        return cast(Fraction, (self.left + self.right) / 2)

    @property
    def center_y(self) -> Fraction:
        return cast(Fraction, (self.top + self.bottom) / 2)


@dataclass(eq=True)
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
    def center_x(self) -> int:
        return (self.left + self.right) // 2

    @property
    def center_y(self) -> int:
        return (self.top + self.bottom) // 2


class ISize(Protocol[NT]):
    width: NT
    height: NT


@dataclass(eq=True)
class ZSize(ISize[int]):
    width: int
    height: int


@dataclass(eq=True)
class QSize(ISize[Fraction]):
    width: Fraction
    height: Fraction


@dataclass(eq=True)
class RSize(ISize[float]):
    width: float
    height: float
