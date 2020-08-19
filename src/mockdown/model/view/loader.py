import json
from typing import Any, Dict, Protocol, TextIO, Type, Literal

import numpy as np

from mockdown.model import IView
from mockdown.model.view import ViewBuilder
from mockdown.types import NT


class IViewLoader(Protocol[NT]):
    def load_dict(self, d: Dict[str, Any]) -> IView[NT]: ...

    def load_file(self, src: TextIO) -> IView[NT]: ...


class ViewLoader(IViewLoader[NT]):
    def __init__(self: IViewLoader[NT], number_type: Type[NT], debug_noise: float = 0):
        self.number_type = number_type
        self.debug_noise = debug_noise

    def load_file(self, src: TextIO) -> IView[NT]:
        d = json.load(src)
        return self.load_dict(d)

    def load_dict(self, data: Dict[str, Any]) -> IView[NT]:
        def recurse(d: Dict[str, Any]) -> ViewBuilder:
            name, rect = d['name'], d['rect']

            if self.debug_noise:
                rect = tuple(rect + self.debug_noise * np.random.randn(4))

            if 'children' not in d or len(d['children']) == 0:
                return ViewBuilder(name=name, rect=rect)
            else:
                child_builders = [recurse(child_dict) for child_dict in d['children']]
                return ViewBuilder(name=name, rect=rect, children=child_builders)

        builder = recurse(data)
        return builder.build(number_type=self.number_type)
