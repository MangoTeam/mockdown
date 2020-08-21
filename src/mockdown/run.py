from __future__ import annotations

import logging
from multiprocessing import Process, Queue
from typing import List, Dict, TypedDict, Literal, Optional, Any, Type, TypeVar

import sympy as sym

from mockdown.constraint.axioms import make_axioms
from mockdown.instantiation import PrologConstraintInstantiator, NumpyConstraintInstantiator, IConstraintInstantiator
from mockdown.learning.noisetolerant import NoiseTolerantLearning, NoiseTolerantLearningConfig
from mockdown.learning.simple import SimpleLearning, SimpleLearningConfig
from mockdown.model import ViewLoader
from mockdown.pruning import BlackBoxPruner, HierarchicalPruner, MarginPruner, DynamicPruner
from mockdown.types import Tuple4, NT

logger = logging.getLogger(__name__)


class MockdownInput(TypedDict):
    examples: List[Dict[str, Any]]
    options: MockdownOptions


class MockdownOptions(TypedDict, total=False):
    numeric_type: Literal["N", "Z", "Q", "R"]

    instantiation_method: Literal['prolog', 'numpy']

    learning_method: Literal['simple', 'noisetolerant']

    pruning_method: Literal['none', 'baseline', 'hierarchical', 'dynamic', 'margins']
    pruning_bounds: Tuple4[Optional[int]]  # min_w min_h max_w max_h

    debug_noise: float
    debug_instantiation: bool

    include_axioms: bool
    debug: bool
    unambig: bool  # what does this mean?...


class MockdownResults(TypedDict):
    constraints: List[Dict[str, str]]
    axioms: List[str]


def run_timeout(*args, **kwargs) -> Optional[MockdownResults]:
    timeout = kwargs.pop('timeout', None)

    # PyCharm's debugger doesn't like subprocesses.
    # When debugging use a timeout of None or 0.
    if not timeout:
        return run(*args, **kwargs)

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


def run(input_data: MockdownInput, options: MockdownOptions, result_queue: Optional[Queue] = None) -> Optional[MockdownResults]:
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
    number_type: Type = {
        'N': sym.Number,
        'R': sym.Float,
        'Q': sym.Rational,
        'Z': sym.Integer
    }[options.get('numeric_type', 'N')]

    instantiator_factory = {
        'prolog': PrologConstraintInstantiator,
        'numpy': NumpyConstraintInstantiator
    }[options.get('instantiation_method', 'prolog')]

    learning_factory = {
        'simple': SimpleLearning,
        'noisetolerant': NoiseTolerantLearning
    }[options.get('learning_method', 'simple')]

    print('using learning method:', options.get('learning_method', 'simple'))

    pruner_factory = {
        'none': lambda x, y, ua: (lambda cns: (cns, None, None)),
        'baseline': BlackBoxPruner,
        'hierarchical': HierarchicalPruner,
        'margins': MarginPruner,
        'dynamic': DynamicPruner
    }[options.get('pruning_method', 'none')]

    debug_noise = options.get('debug_noise', 0)

    unambig = options.get('unambig', False)

    loader = ViewLoader(number_type=number_type, debug_noise=debug_noise)

    # 1. Load Examples
    examples = [loader.load_dict(ex_data) for ex_data in examples_data]

    # Check that examples are isomorphic.
    if debug and len(examples) > 0:
        for example in examples[1:]:
            example.is_isomorphic(examples[0], include_names=True)

    # 2. Instantiate Templates
    instantiator = instantiator_factory(examples)
    templates = instantiator.instantiate()

    if options.get('debug_instantiation'):
        nl = '\n'
        tb = '\t'
        logger.debug(f"TEMPLATES:\n{nl.join(map(lambda t: f'{tb}{t}', templates))}")
        return {
            'constraints': [tpl.to_dict() for tpl in templates],
            'axioms': []
        }

    # 3. Learn Constants.
    learning_config: Any = {
        'simple': SimpleLearningConfig(),
        'noisetolerant': NoiseTolerantLearningConfig(
            sample_count=len(examples),
            max_offset=max((max(ex.width, ex.height) for ex in examples))
        )
    }[options.get('learning_method', 'simple')]

    learning = learning_factory(samples=examples, templates=templates, config=learning_config)
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
