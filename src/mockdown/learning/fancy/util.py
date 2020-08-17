from typing import Tuple, Dict, Iterator

import numpy as np  # type: ignore


def q2cf(a: int, b: int) -> Iterator[int]:
    """Yields the continued fraction expansion of the rational represented by n1/n2."""
    while b:
        a, (res, b) = b, divmod(a, b)
        yield res


def sb_depth(a: int, b: int) -> int:
    """Returns the Stern-Brocot depth of the rationals a/b."""
    return sum(list(q2cf(a, b)))


def candidate_bounds(x: np.ndarray, y: np.ndarray, map_result: Dict[str, np.ndarray]) -> Tuple[float, float, float, float]:
    # Note: x and y should be in sorted order!

    sigma = np.exp(map_result['sigma'])

    x1, x2 = min(x), max(x)
    y1, y2 = min(y), max(y)

    # a = (y2 - y1) / (x2 - x1)
    a1 = ((y2 + 3 * sigma) - (y1 - 3 * sigma)) / (x2 - x1)
    a2 = ((y2 - 3 * sigma) - (y1 + 3 * sigma)) / (x2 - x1)

    # b = y - mx (where x,y = x1, y1 or x2, y2, equivalently)
    b1 = y1 - a1 * x1
    b2 = y1 - a2 * x1

    return min(a1, a2), max(a1, a2), min(b1, b2), max(b1, b2)


def candidate_bounds_indices(a_space: np.ndarray,
                             b_space: np.ndarray,
                             a_lower: float,
                             a_upper: float,
                             b_lower: float,
                             b_upper: float) -> Tuple[int, int, int, int]:
    a_i_lower = np.abs(a_space - a_lower).argmin()
    a_i_upper = np.abs(a_space - a_upper).argmin()
    b_i_lower = np.abs(b_space - b_lower).argmin()
    b_i_upper = np.abs(b_space - b_upper).argmin()
    return a_i_lower, a_i_upper, b_i_lower, b_i_upper
