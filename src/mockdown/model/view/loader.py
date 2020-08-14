import json
from typing import Any, Dict, Protocol, TextIO, Type, Literal

from mockdown.model import IView
from mockdown.model.view import ViewBuilder
from mockdown.types import NT


class IViewLoader(Protocol[NT]):
    def load_dict(self, d: Dict[str, Any]) -> IView[NT]: ...

    def load_file(self, src: TextIO) -> IView[NT]: ...


class ViewLoader(IViewLoader[NT]):
    def __init__(self: IViewLoader[NT], number_type: Type[NT]):
        self.number_type = number_type

    def load_file(self, src: TextIO) -> IView[NT]:
        d = json.load(src)
        return self.load_dict(d)

    def load_dict(self, data: Dict[str, Any]) -> IView[NT]:
        def recurse(d: Dict[str, Any]) -> ViewBuilder:
            if 'children' not in d or len(d['children']) == 0:
                return ViewBuilder(name=d['name'], rect=d['rect'])
            else:
                child_builders = [recurse(child_dict) for child_dict in d['children']]
                return ViewBuilder(name=d['name'], rect=d['rect'], children=child_builders)

        builder = recurse(data)
        return builder.build(number_type=self.number_type)
