from dataclasses import dataclass

TINY = 1e-20


@dataclass(frozen=True)
class FancyLearningConfig:
    # Parameters
    sample_count: int

    # The p-value of a model goodness-of-fit test below which learning should be rejected.
    cutoff_fit: float = 0.05

    # The relative standard deviation of data above which template learning should be rejected.
    # Can be interpreted as a percentage, I think.
    cutoff_rsd: int = 0.05

    b_min: int = -1000
    b_max: int = +1000

    max_denominator: int = 100
