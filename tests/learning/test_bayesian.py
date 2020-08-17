import numpy as np
import pymc3 as pm

from mockdown.learning.fancy.models import mk_relaxed_model_linear, mk_relaxed_model_constant
from mockdown.learning.fancy.types import FancyLearningConfig


def test_relaxed_model() -> None:
    config = FancyLearningConfig(sample_count=3)

    model = mk_relaxed_model_linear(config)

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
    assert np.isclose(map_result['sigma'], 0, atol=1e-3)  # see np.isclose notes for why we don't use the default.


def test_relaxed_model_constant() -> None:
    config = FancyLearningConfig(sample_count=3)

    model = mk_relaxed_model_constant(config)

    with model:
        pm.set_data({'y_data': [10, 10, 10]})
        map_result1 = pm.find_MAP()

        pm.set_data({'y_data': [20, 20, 20]})
        map_result2 = pm.find_MAP()

    assert np.isclose(map_result1['b'], 10)
    assert np.isclose(map_result1['sigma'], 0, atol=1e-3)  # see np.isclose notes for why we don't use the default.

    assert np.isclose(map_result2['b'], 20)
    assert np.isclose(map_result2['sigma'], 0, atol=1e-3)  # see np.isclose notes for why we don't use the default.
