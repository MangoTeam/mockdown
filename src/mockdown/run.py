from __future__ import annotations

import logging
from cProfile import Profile
from datetime import datetime
from multiprocessing import Process, Queue
from pprint import pprint
from typing import List, Dict, TypedDict, Literal, Optional, Any, Type

import sympy as sym
from more_itertools import flatten

from mockdown.constraint.axioms import make_axioms
from mockdown.instantiation import NumpyConstraintInstantiator, get_prolog_instantiator_factory
from mockdown.learning.noisetolerant import NoiseTolerantLearning, NoiseTolerantLearningConfig
from mockdown.learning.simple import SimpleLearning, SimpleLearningConfig, HeuristicLearning
from mockdown.model import ViewLoader
from mockdown.pruning import BlackBoxPruner, HierarchicalPruner, MarginPruner, DynamicPruner
from mockdown.types import Tuple4, PROFILE

logger = logging.getLogger(__name__)
nl = '\n'
tb = '\t'


class MockdownInput(TypedDict):
    examples: List[Dict[str, Any]]
    options: MockdownOptions


class MockdownOptions(TypedDict, total=False):
    input_format: Literal['default', 'bench']
    numeric_type: Literal["N", "Z", "Q", "R"]

    instantiation_method: Literal['prolog', 'numpy']

    learning_method: Literal['simple', 'heuristic', 'noisetolerant']

    pruning_method: Literal['none', 'baseline', 'hierarchical', 'dynamic', 'margins']
    pruning_bounds: Tuple4[Optional[int]]  # min_w min_h max_w max_h

    debug_noise: float
    debug_visibilities: bool
    debug_instantiation: bool

    num_examples: Optional[int] = None  # None means all

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


def run(input_data: MockdownInput, options: MockdownOptions, result_queue: Optional[Queue] = None) \
        -> Optional[MockdownResults]:
    """
    This command's guts are pulled out here so they can be called from Python
    directly, as well as from the CLI.

    It is in its own file to prevent import cycles between cli and app!
    """
    logger.info(f"Running with options: {options}")

    debug = options.get('debug', False)
    input_format = options.get('input_format', 'default')

    if input_format == 'default':
        examples_data = input_data["examples"]
    elif input_format == 'bench':
        examples_data = input_data["train"]

    if num_examples := options.get('num_examples', None):
        logger.warn(f"Only using the first {num_examples} examples in input data.")
        examples_data = examples_data[:num_examples]

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
        'prolog': get_prolog_instantiator_factory(),
        'numpy': NumpyConstraintInstantiator
    }[options.get('instantiation_method', 'numpy')]

    learning_factory = {
        'simple': SimpleLearning,
        'heuristic': HeuristicLearning,
        'noisetolerant': NoiseTolerantLearning
    }[options.get('learning_method', 'noisetolerant')]

    # print('using learning method:', options.get('learning_method', 'simple'))

    pruner_factory = {
        'none': lambda x, y, ua: (lambda cands: ([cand.constraint for cand in cands], None, None)),
        'baseline': BlackBoxPruner,
        'hierarchical': HierarchicalPruner,
        # 'margins': MarginPruner,
        # 'dynamic': DynamicPruner
    }[options.get('pruning_method', 'hierarchical')]

    debug_noise = options.get('debug_noise', 0)
    unambig = options.get('unambig', False)

    loader = ViewLoader(number_type=number_type, input_format=input_format, debug_noise=debug_noise)

    # 1. Load Examples
    examples = [loader.load_dict(ex_data) for ex_data in examples_data]

    # Check that examples are isomorphic.
    if debug and len(examples) > 0:
        for example in examples[1:]:
            example.is_isomorphic(examples[0], include_names=True)

    # 2. Instantiate Templates
    instantiator = instantiator_factory(examples)

    if options.get('debug_visibilities'):
        return {
            'constraints': [],
            'axioms': [],
            'visibilities': instantiator.detect_visibilities()
        }

    instantiation_start = datetime.now()
    if PROFILE:
        pr = Profile()
        pr.enable()
    templates = instantiator.instantiate()
    if PROFILE:
        pr.disable()
        pr.dump_stats('profile-instantiation.pstat')
    instantiation_end = datetime.now()
    # logger.info(f"Instantiation finished in {instantiation_end - instantiation_start}s.")

    logger.debug(len(templates))
    # logger.debug(f"TEMPLATES:\n{nl.join(map(lambda t: f'{tb}{t}', sorted(templates)))}")
    # logger.info(f"TEMPLATES:\n{nl.join(map(lambda t: f'{t.y_id}{tb}{t.x_id}{tb}{t.kind}', sorted(templates)))}")

    if options.get('debug_instantiation'):
        print(len(templates))
        return {
            'constraints': [tpl.to_dict() for tpl in templates],
            'axioms': []
        }

    # 3. Learn Constants.
    learning_config: Any = {
        'simple': SimpleLearningConfig(),
        'heuristic': SimpleLearningConfig(),
        'noisetolerant': NoiseTolerantLearningConfig(
            sample_count=len(examples),
            max_offset=max((max(ex.width, ex.height) for ex in examples)) + 10  # some wiggle room.
        )
    }[options.get('learning_method', 'simple')]

    if PROFILE:
        pr = Profile()
        pr.enable()
    learning = learning_factory(samples=examples, templates=templates, config=learning_config)
    candidates = list(flatten(learning.learn()))
    if PROFILE:
        pr.disable()
        pr.dump_stats('profile-learning.pstat')

    # logger.info(f"CANDIDATES:\n{nl.join(map(lambda c: f'{c.constraint}{tb}{c.score}', sorted(candidates)))}")

    # 4. Pruning.
    if PROFILE:
        pr = Profile()
        pr.enable()

    prune = pruner_factory(examples, bounds_dict, unambig)
    pruned_constraints, _, _ = prune(candidates)

    if PROFILE:
        pr.disable()
        pr.dump_stats('profile-pruning.pstat')

    logger.info(f"KEPT:\n{nl.join(map(lambda c: f'{c}', sorted(pruned_constraints)))}")
    logger.info(f"PRUNED:\n{nl.join(map(lambda c: f'{c}', sorted(set([x.constraint for x in candidates]) - set(pruned_constraints))))}")

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
