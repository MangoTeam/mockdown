from fractions import Fraction
from functools import lru_cache
from math import ceil, floor, isclose
from typing import List, SupportsFloat

import numpy as np  # type: ignore


@lru_cache
def farey(n: int = 100) -> np.ndarray:
    return np.array([Fraction(0, 1)] + sorted({
        Fraction(m, k)
        for k in range(1, n + 1)
        for m in range(1, k + 1)
    }), dtype=np.object)


@lru_cache
def ext_farey(n: int = 100) -> np.ndarray:
    """
    Farey sequence with its reversed reciprocals appended.
    Extends the sequence from 0-1 to 0-n.
    """
    f = farey(n)
    return np.array(f + [Fraction(a.q, a.p) for a in reversed(f[1:-1])], dtype=np.object)


@lru_cache
def z_ball(center: SupportsFloat, radius: SupportsFloat) -> np.ndarray:
    center, radius = float(center), float(radius)
    return np.arange(ceil(center - radius), floor(center + radius), dtype=np.int)
