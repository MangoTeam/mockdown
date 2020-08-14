from dataclasses import dataclass

TINY = 1e-20


@dataclass(frozen=True)
class BayesianLearningConfig:
    # Parameters
    sample_count: int

    # Constants
    eps_px: int = 3

    b_min: int = -1000
    b_max: int = +1000

    max_denominator: int = 100
