from dataclasses import dataclass
from functools import lru_cache
import numpy as np  # type: ignore
import scipy.stats as st

from mockdown.learning.noisetolerant.math import ext_farey, z_ball, sb_depth

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
    expected_depth: int = 5

    a_alpha: float = 0.05
    b_alpha: float = 0.05

    @property  # type: ignore
    @lru_cache  # type: ignore
    def a_space(self) -> np.ndarray:
        return ext_farey(self.max_denominator)

    @property  # type: ignore
    @lru_cache  # type: ignore
    def b_space(self) -> np.ndarray:
        return z_ball(0, self.max_offset)

    @property  # type: ignore
    @lru_cache  # type: ignore
    def sb_depth_hist(self) -> np.ndarray:
        sb_depths = np.vectorize(lambda a: sb_depth(a))(self.a_space)
        sb_depth_hist, _ = np.histogram(sb_depths, bins=self.max_denominator + 1)
        return sb_depth_hist

    @property  # type: ignore
    @lru_cache  # type: ignore
    def depth_prior(self) -> np.ndarray:
        max_d, exp_d = self.max_denominator, self.expected_depth
        n = max_d
        alpha = exp_d + 1
        beta = (max_d - exp_d) + 1

        sb_depths = np.vectorize(lambda a: sb_depth(a))(self.a_space)
        sb_depth_hist, _ = np.histogram(sb_depths, bins=max_d + 1)
        betabin = np.vectorize(lambda k: st.betabinom.pmf(k, n, alpha, beta))(np.arange(0, max_d + 1, 1))

        return betabin[sb_depths] * (1/sb_depth_hist)[sb_depths]


