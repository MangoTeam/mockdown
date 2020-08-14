from typing import Dict

import numpy as np  # type: ignore
import pymc3 as pm  # type: ignore
import theano as th  # type: ignore

from mockdown.learning.bayesian.types import BayesianLearningConfig, TINY

# noinspection PyTypeChecker
from mockdown.learning.math.sequences import ext_farey


def mk_relaxed_model(config: BayesianLearningConfig) -> pm.Model:
    model = pm.Model()

    with model:
        x_data = pm.Data('x_data', np.zeros(config.sample_count))
        y_data = pm.Data('y_data', np.zeros(config.sample_count))

        sigma = pm.HalfCauchy('sigma', beta=(config.eps_px + TINY) / 3)

        b = pm.Uniform('b', lower=config.b_min, upper=config.b_max)
        a = pm.Uniform('a', lower=0, upper=config.max_denominator)

        y = pm.Normal('y', mu=a * x_data + b, sigma=sigma, observed=y_data)

    return model


def mk_full_model(config: BayesianLearningConfig) -> pm.Model:
    f_r = ext_farey(config.max_denominator)

    a_space_np = np.array(f_r, dtype=np.object)
    a_space_th = th.shared(np.array([(frac.p, frac.q) for frac in f_r]))

    b_space_np = np.arange(config.b_min, config.b_max, 1, dtype=np.int)
    b_space_th = th.shared(b_space_np)

    model = pm.Model()

    with model:
        x_data = pm.Data('x_data', np.zeros(config.sample_count))
        y_data = pm.Data('y_data', np.zeros(config.sample_count))

        b_i = pm.DiscreteUniform('b_i', lower=0, upper=len(b_space_np))
        b = pm.Deterministic('b', b_space_th[b_i])

        # todo: put proper bias back in (accidentally deleted in notebook...)!
        a_i = pm.DiscreteUniform('a_i', lower=0, upper=len(a_space_np))
        a_p = pm.Deterministic('a_p', a_space_th[a_i][0])
        a_q = pm.Deterministic('a_q', a_space_th[a_i][1])

        y = pm.Normal('y', mu=(a_p / a_q) * x_data + b, sigma=(config.eps_px + TINY) / 3, observed=y_data)

    return model
