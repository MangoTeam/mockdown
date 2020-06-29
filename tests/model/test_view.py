import sympy as sym

from mockdown.model import ViewLoader


def test_view_is_isomorphic() -> None:
    loader = ViewLoader(number_type=sym.Integer)
    v1 = loader.load_dict({
        'name': 'root',
        'rect': (0, 0, 100, 100),
        'children': [{
            'name': 'child',
            'rect': (10, 10, 90, 90)
        }]
    })

    v2 = loader.load_dict({
        'name': 'root',
        'rect': (0, 0, 200, 100),
        'children': [{
            'name': 'child',
            'rect': (10, 10, 190, 90)
        }]
    })

    v3 = loader.load_dict({
        'name': 'raiz',
        'rect': (0, 0, 100, 200),
        'children': [{
            'name': 'niño',
            'rect': (10, 10, 90, 190)
        }]
    })

    # Reflexivity
    assert v1.is_isomorphic(v1)

    # Sanity
    assert v1.is_isomorphic(v2)

    assert v1.is_isomorphic(v2, include_names=False)
    assert v2.is_isomorphic(v3, include_names=False)


