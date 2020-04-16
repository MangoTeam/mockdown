import json
from abc import ABC
from fractions import Fraction
from typing import Any, Callable, Dict, Protocol, SupportsFloat, SupportsInt, TextIO, Union, cast

from mockdown.model import IView
from mockdown.model.view.builder import QViewBuilder, RViewBuilder, ZViewBuilder
from mockdown.typing import NT, Tuple4


class IViewLoader(Protocol[NT]):
    def load_dict(self, d: Dict[str, Any]) -> IView[NT]: ...

    def load_file(self, src: TextIO) -> IView[NT]: ...


class _BaseViewLoader(IViewLoader[NT], ABC):
    def load_file(self, src: TextIO) -> IView[NT]:
        d = json.load(src)
        return self.load_dict(d)


class RViewLoader(_BaseViewLoader[float]):
    def load_dict(self, d: Dict[str, Any]) -> IView[float]:
        def recurse(d: Dict[str, Any]) -> RViewBuilder:
            if 'children' not in d or len(d['children']) == 0:
                return RViewBuilder(name=d['name'], rect=d['rect'])
            else:
                child_builders = [recurse(child_dict) for child_dict in d['children']]
                return RViewBuilder(name=d['name'], rect=d['rect'], children=child_builders)

        builder = recurse(d)
        return builder.build()


class QViewLoader(_BaseViewLoader[Fraction]):
    def __init__(self, max_denominator: int = 1000000):
        self.max_denominator = max_denominator

    def _rationalize(self, x: Union[float, int, str]) -> Fraction:
        return Fraction(x).limit_denominator(self.max_denominator)

    def load_dict(self, d: Dict[str, Any]) -> IView[Fraction]:
        def recurse(d: Dict[str, Any]) -> QViewBuilder:
            rect = tuple(map(self._rationalize, d['rect']))
            assert len(rect) == 4
            rect = cast(Tuple4[Fraction], rect)  # shut up, mypy

            if 'children' not in d or len(d['children']) == 0:
                return QViewBuilder(name=d['name'], rect=rect)
            else:
                child_builders = [recurse(child_dict) for child_dict in d['children']]
                return QViewBuilder(name=d['name'], rect=d['rect'], children=child_builders)

        builder = recurse(d)
        return builder.build()


class ZViewLoader(_BaseViewLoader[int]):
    @staticmethod
    def strictly_ints(n: SupportsFloat) -> int:
        if isinstance(n, int):
            return n
        elif isinstance(n, SupportsInt) and float(n) == float(int(n)):
            return int(n)
        else:
            raise Exception("Only ints allowed!")

    def __init__(self, integerize_fn: Callable[[SupportsFloat], int] = strictly_ints):
        # You could also use some rounding/ceil/floor...
        self.integerize_fn = integerize_fn

    def load_dict(self, d: Dict[str, Any]) -> IView[int]:
        def recurse(d: Dict[str, Any]) -> ZViewBuilder:
            rect = tuple(map(self.integerize_fn, d['rect']))
            assert len(rect) == 4
            rect = cast(Tuple4[int], rect)  # shut up, mypy

            if 'children' not in d or len(d['children']) == 0:
                return ZViewBuilder(name=d['name'], rect=rect)
            else:
                child_builders = [recurse(child_dict) for child_dict in d['children']]
                return ZViewBuilder(name=d['name'], rect=rect, children=child_builders)

        builder = recurse(d)
        return builder.build()
