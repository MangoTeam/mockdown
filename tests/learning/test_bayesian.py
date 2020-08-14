import numpy as np
import pymc3 as pm
import pytest
from hypothesis import given
from hypothesis import strategies as gen

from mockdown.learning.bayesian.models import mk_relaxed_model, candidate_bounds
from mockdown.learning.bayesian.types import BayesianLearningConfig


def test_relaxed_model() -> None:
    config = BayesianLearningConfig(sample_count=3)

    model = mk_relaxed_model(config)

    x = np.array([1, 2, 3])
    y = 2 * x + 10

    with model:
        pm.set_data({
            'x_data': x,
            'y_data': y,
        })

        map_result = pm.find_MAP()

    assert np.isclose(map_result['a'], 2)
    assert np.isclose(map_result['b'], 10)

    print(candidate_bounds(x, y, map_result))
