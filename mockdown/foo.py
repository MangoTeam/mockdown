from abc import abstractmethod
from dataclasses import dataclass
from typing import Generic, NoReturn, Protocol, TypeVar


def unreachable(x: NoReturn) -> NoReturn:
    assert False, "Unhandled type: {}".format(type(x).__name__)


# T is constrained to be either int or str.
T = TypeVar('T', int, str)
T_co = TypeVar('T_co', int, str, covariant=True)
T_contra = TypeVar('T_contra', int, str, contravariant=True)


class IWidget(Protocol[T_co]):
    @property
    @abstractmethod
    def foo(self) -> T_co: ...


@dataclass
class IntWidget(IWidget[int]):
    foo: int


@dataclass
class StrWidget(IWidget[str]):
    foo: str


class WidgetFactory(Generic[T]):
    materials: T

    def __init__(self, materials: T):
        self.materials = materials

    def create(self) -> IWidget[T]:
        m = self.materials

        if isinstance(m, int):
            return IntWidget(m)
        elif isinstance(self.materials, str):
            return StrWidget(m)
        else:
            unreachable(m)
