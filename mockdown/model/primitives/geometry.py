from __future__ import annotations

from abc import abstractmethod
from dataclasses import dataclass
from fractions import Fraction
from typing import Protocol, TypeVar, cast, runtime_checkable

from ...typing import NT_co


@runtime_checkable
class IRect(Protocol[NT_co]):
    @property
    @abstractmethod
    def left(self) -> NT_co: ...

    @property
    @abstractmethod
    def top(self) -> NT_co: ...

    @property
    @abstractmethod
    def right(self) -> NT_co: ...

    @property
    @abstractmethod
    def bottom(self) -> NT_co: ...

    @property
    @abstractmethod
    def width(self) -> NT_co: ...

    @property
    @abstractmethod
    def height(self) -> NT_co: ...

    @property
    @abstractmethod
    def center_x(self) -> NT_co: ...

    @property
    @abstractmethod
    def center_y(self) -> NT_co: ...

    @property
    @abstractmethod
    def size(self) -> ISize[NT_co]: ...


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
    def center_x(self) -> float:
        return (self.left + self.right) / 2

    @property
    def center_y(self) -> float:
        return (self.top + self.bottom) / 2


@dataclass(frozen=True)
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
    def center_x(self) -> int:
        return (self.left + self.right) // 2

    @property
    def center_y(self) -> int:
        return (self.top + self.bottom) // 2


class ISize(Protocol[NT_co]):
    @property
    @abstractmethod
    def width(self) -> NT_co: ...

    @property
    @abstractmethod
    def height(self) -> NT_co: ...


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
