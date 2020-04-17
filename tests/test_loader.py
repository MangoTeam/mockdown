from fractions import Fraction

import pytest  # type: ignore

from mockdown.model import QViewLoader, ZViewLoader


class TestZViewLoader:
    def test_strictly_ints(self) -> None:
        loader = ZViewLoader(integerize_fn=ZViewLoader.strictly_ints)
        view = loader.load_dict({
            'name': 'root',
            'rect': [0, 0, 100, 100]
        })

        view = loader.load_dict({
            'name': 'root',
            'rect': [0.0, 0.0, 100.0, 100.0]
        })

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
