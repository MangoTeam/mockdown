import sympy as sym

from mockdown.model import ViewLoader, ViewBuilder as V


class TestViewLoader:
    def test_loading_ints(self) -> None:
        loader = ViewLoader(number_type=sym.Integer)
        view = loader.load_dict({
            'name': 'root',
            'rect': [0, 0, 100, 100],
            'children': [{
                'name': 'child',
                'rect': [10, 10, 90, 90]
            }]
        })

        assert view == V('root', (0, 0, 100, 100), [
            V('child', (10, 10, 90, 90))
        ]).build(number_type=sym.Integer)

        view = loader.load_dict({
            'name': 'root',
            'rect': [0.0, 0.0, 100.0, 100.0]
        })

        assert view == V('root', (0, 0, 100, 100)).build(number_type=sym.Integer)
