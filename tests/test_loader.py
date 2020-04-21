from fractions import Fraction

import pytest  # type: ignore

from mockdown.model import QViewLoader, ZViewLoader, ZViewBuilder
from mockdown.model.view.loader import strictly_ints

ZV = ZViewBuilder


class TestZViewLoader:
    def test_strictly_ints(self) -> None:
        loader = ZViewLoader(integerize_fn=strictly_ints)
        view = loader.load_dict({
            'name': 'root',
            'rect': [0, 0, 100, 100],
            'children': [{
                'name': 'child',
                'rect': [10, 10, 90, 90]
            }]
        })

        assert view == ZV('root', (0, 0, 100, 100), [
            ZV('child', (10, 10, 90, 90))
        ]).build()

        view = loader.load_dict({
            'name': 'root',
            'rect': [0.0, 0.0, 100.0, 100.0]
        })

        assert view == ZV('root', (0, 0, 100, 100)).build()

        with pytest.raises(Exception):
            view = loader.load_dict({
                'name': 'root',
                'rect': [0.0, 0.0, 100.5, 100.5]
            })


class TestQViewLoader:
    def test_string_fractions(self) -> None:
        loader = QViewLoader()
        view = loader.load_dict({
            'name': 'root',
            'rect': [0, 0, '1/2', '1/2']
        })

        view = loader.load_dict({
            'name': 'root',
            'rect': [0.0, 0.0, 0.5, 0.5]
        })
        assert view.right == Fraction(1, 2)
        assert view.bottom == Fraction(1, 2)
