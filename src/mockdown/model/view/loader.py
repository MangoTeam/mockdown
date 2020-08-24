import json
from typing import Any, Dict, Protocol, TextIO, Type, Literal

import numpy as np

from mockdown.model import IView
from mockdown.model.view import ViewBuilder
from mockdown.types import NT, unreachable


class IViewLoader(Protocol[NT]):
    def load_dict(self, d: Dict[str, Any]) -> IView[NT]: ...

    def load_file(self, src: TextIO) -> IView[NT]: ...


class ViewLoader(IViewLoader[NT]):
    def __init__(self: IViewLoader[NT],
                 number_type: Type[NT],
                 input_format: Literal['default', 'bench'] = 'default',
                 debug_noise: float = 0):
        self.number_type = number_type
        self.input_format = input_format
        self.debug_noise = debug_noise

    def load_file(self, src: TextIO) -> IView[NT]:
        d = json.load(src)
        return self.load_dict(d)

    def load_dict(self, data: Dict[str, Any]) -> IView[NT]:
        def recurse(d: Dict[str, Any]) -> ViewBuilder:
            if self.input_format == 'default':
                name, rect = d['name'], d['rect']
            elif self.input_format == 'bench':
                name = d['name']
                rect = (d['left'], d['top'], d['left'] + d['width'], d['top'] + d['height'])
            else:
                unreachable(self.input_format)

            if self.debug_noise:
                rect = tuple(rect + self.debug_noise * np.random.randn(4))

            if 'children' not in d or len(d['children']) == 0:
                return ViewBuilder(name=name, rect=rect)
            else:
                child_builders = [recurse(child_dict) for child_dict in d['children']]
                return ViewBuilder(name=name, rect=rect, children=child_builders)

        builder = recurse(data)
        return builder.build(number_type=self.number_type)
