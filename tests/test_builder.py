from typing import TypeVar, Type

import sympy as sym

from mockdown.model import ViewBuilder as V, IView
from mockdown.typing import NT


class TestViewBuilder:
    def test_dependent_typing(self) -> None:
        vz: IView[sym.Integer] = V(
            'root',
            (0, 0, 100, 100)
        ).build(number_type=sym.Integer)

        assert isinstance(vz.rect.left, sym.Integer)
        assert isinstance(vz.rect.top, sym.Integer)
        assert isinstance(vz.rect.right, sym.Integer)
        assert isinstance(vz.rect.bottom, sym.Integer)

        vr: IView[sym.Float] = V(
            'root',
            (0, 0, 100, 100)
        ).build(number_type=sym.Float)

        assert isinstance(vr.rect.left, sym.Float)
        assert isinstance(vr.rect.top, sym.Float)
        assert isinstance(vr.rect.right, sym.Float)
        assert isinstance(vr.rect.bottom, sym.Float)
