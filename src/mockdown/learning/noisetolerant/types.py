from dataclasses import dataclass
from functools import lru_cache
import numpy as np  # type: ignore

from mockdown.learning.noisetolerant.math import ext_farey, z_ball

TINY = 1e-20


@dataclass(frozen=True)
class NoiseTolerantLearningConfig:
    # Parameters
    sample_count: int

    # The p-value of a model goodness-of-fit test below which learning should be rejected.
    cutoff_fit: float = 0.05

    # The standard deviation of data above which template learning should be rejected.
    cutoff_spread: int = 3

    max_offset: int = 1000
    max_denominator: int = 100

    a_alpha: float = 0.05
    b_alpha: float = 0.05

    @property  # type: ignore
    @lru_cache
    def a_space(self) -> np.ndarray:
        return ext_farey(self.max_denominator)

    @property  # type: ignore
    @lru_cache
    def b_space(self) -> np.ndarray:
        return z_ball(0, self.max_offset)
