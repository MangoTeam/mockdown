import json
from abc import ABC
from typing import Any, Dict, Protocol, TextIO

from sympy import Number  # type: ignore

from mockdown.model import IView
from mockdown.model.view import ViewBuilder
from mockdown.model.view.typing import NumberFactory
from mockdown.typing import NT


class IViewLoader(Protocol[NT]):
    def load_dict(self, d: Dict[str, Any]) -> IView[NT]: ...

    def load_file(self, src: TextIO) -> IView[NT]: ...


class _BaseViewLoader(IViewLoader[NT], ABC):
    def load_file(self, src: TextIO) -> IView[NT]:
        d = json.load(src)
        return self.load_dict(d)


class ViewLoader(_BaseViewLoader[Number]):
    def __init__(self, number_factory: NumberFactory):
        self.number_factory = number_factory

    def load_dict(self, data: Dict[str, Any]) -> IView[NT]:
        def recurse(d: Dict[str, Any]) -> ViewBuilder:
            if 'children' not in d or len(d['children']) == 0:
                return ViewBuilder(name=d['name'], rect=d['rect'])
            else:
                child_builders = [recurse(child_dict) for child_dict in d['children']]
                return ViewBuilder(name=d['name'], rect=d['rect'], children=child_builders)

        builder = recurse(data)
        return builder.build(number_factory=self.number_factory)
