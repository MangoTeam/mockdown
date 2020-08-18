from __future__ import annotations

import logging
from multiprocessing import Process, Queue
from typing import List, Dict, TypedDict, Literal, Optional, Any, Tuple

import sympy as sym

from mockdown.constraint.axioms import make_axioms
from mockdown.instantiation import VisibilityConstraintInstantiator
from mockdown.learning.fancy import FancyLearning
from mockdown.learning.simple import SimpleLearning
from mockdown.model import ViewLoader
from mockdown.pruning import BlackBoxPruner, HierarchicalPruner, MarginPruner, DynamicPruner
from mockdown.types import Tuple4

logger = logging.getLogger(__name__)


class MockdownInput(TypedDict):
    examples: List[Dict[str, Any]]
    options: MockdownOptions


class MockdownOptions(TypedDict, total=False):
    numeric_type: Literal["N", "Z", "Q", "R"]

    learning_method: Literal['simple', 'fancy']

    pruning_method: Literal['none', 'baseline', 'hierarchical', 'dynamic', 'margins']
    pruning_bounds: Tuple4[Optional[int]]  # min_w min_h max_w max_h

    synthetic_noise: Optional[Tuple[float, float]]

    include_axioms: bool
    debug: bool
    unambig: bool  # what does this mean?...


class MockdownResults(TypedDict):
    constraints: List[Dict[str, str]]
    axioms: List[str]


def run_timeout(*args, **kwargs) -> Optional[MockdownResults]:
    timeout = kwargs.pop('timeout', None)

    queue = Queue()
    kwargs.update({'result_queue': queue})

    p = Process(target=run, args=args, kwargs=kwargs)
    p.start()
    p.join(timeout)
    if p.is_alive():
        p.kill()
        logger.warn(f"Synthesis timed out after {timeout}s.")
        return None

    return queue.get()


def run(input_data: MockdownInput, options: MockdownOptions, result_queue: Optional[Queue] = None) -> Optional[
    MockdownResults]:
    """
    This command's guts are pulled out here so they can be called from Python
    directly, as well as from the CLI.

    It is in its own file to prevent import cycles between cli and app!
    """
    debug = options.get('debug', False)

    examples_data = input_data["examples"]
    bounds = options.get('pruning_bounds', (None, None, None, None))
    bounds_dict = {
        'min_w': bounds[0],
        'min_h': bounds[1],
        'max_w': bounds[2],
        'max_h': bounds[3]
    }

    # Note: sym.Number _should_ generally "do the right thing"...
    number_type = {
        'N': sym.Number,
        'R': sym.Float,
        'Q': sym.Rational,
        'Z': sym.Integer
    }[options.get('numeric_type', 'N')]

    learning_factory = {
        'simple': SimpleLearning,
        'fancy': FancyLearning
    }[options.get('learning_method', 'simple')]

    pruner_factory = {
        'none': lambda x, y, ua: (lambda cns: (cns, None, None)),
        'baseline': BlackBoxPruner,
        'hierarchical': HierarchicalPruner,
        'margins': MarginPruner,
        'dynamic': DynamicPruner
    }[options.get('pruning_method', 'none')]

    unambig = options.get('unambig', False)

    loader = ViewLoader(number_type=number_type)
    instantiator = VisibilityConstraintInstantiator()

    # 1. Load Examples
    examples = [loader.load_dict(ex_data) for ex_data in examples_data]

    # Check that examples are isomorphic.
    if debug and len(examples) > 0:
        for example in examples[1:]:
            example.is_isomorphic(examples[0], include_names=True)

    # 2. Instantiate Templates
    templates = instantiator.instantiate(examples)

    # 3. Learn Constants.
    learning = learning_factory(samples=examples, templates=templates)
    constraints = [candidate.constraint
                   for candidates in learning.learn()
                   for candidate in candidates]

    # 4. Pruning.
    prune = pruner_factory(examples, bounds_dict, unambig)
    pruned_constraints, _, _ = prune(constraints)

    result: MockdownResults = {
        'constraints': [cn.to_dict() for cn in pruned_constraints],
        'axioms': []
    }

    if options.get('include_axioms', False):
        result['axioms'] = list(map(str, make_axioms(list(examples[0]))))

    if result_queue:
        result_queue.put(result)
        return None
    else:
        return result
