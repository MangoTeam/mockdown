import json
from typing import TextIO, List, Dict, TypedDict, Union, Literal, Optional

import sympy as sym

from mockdown.constraint.axioms import make_axioms
from mockdown.instantiation import VisibilityConstraintInstantiator
from mockdown.learning.simple import SimpleLearning
from mockdown.model import ViewLoader
from mockdown.pruning import BlackBoxPruner, HierarchicalPruner


class MockdownOptions(TypedDict, total=False):
    numeric_type: Literal["N", "Z", "Q", "R"]
    pruning_method: Literal["none", "baseline", "hierarchical"]
    include_axioms: bool
    debug: bool


class MockdownResult(TypedDict):
    constraints: List[Dict[str, str]]
    axioms: Optional[List[str]]


def run(input_io: TextIO, options: MockdownOptions) -> MockdownResult:
    """
    This command's guts are pulled out here so they can be called from Python
    directly, as well as from the CLI.

    It is in its own file to prevent import cycles between cli and app!
    """
    debug = options.get('debug', False)

    input_data = json.load(input_io)

    examples_data = input_data["examples"]
    bounds = input_data.get('bounds', {})

    # Note: sym.Number _should_ generally "do the right thing"...
    number_type = {
        'N': sym.Number,
        'R': sym.Float,
        'Q': sym.Rational,
        'Z': sym.Integer
    }[options.get('numeric_type', 'N')]

    pruner_factory = {
        'none': lambda x, y: (lambda cns: cns),
        'baseline': BlackBoxPruner,
        'hierarchical': HierarchicalPruner,
    }[options.get('pruning_method', 'none')]

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
    learning = SimpleLearning(samples=examples, templates=templates)
    constraints = [candidate.constraint
                   for candidates in learning.learn()
                   for candidate in candidates]

    # 4. Pruning.
    prune = pruner_factory(examples, bounds)
    pruned_constraints = prune(constraints)

    result: MockdownResult = {
        'constraints': [cn.to_dict() for cn in pruned_constraints],
        'axioms': None
    }

    if options.get('include_axioms', False):
        result['axioms'] = list(map(str, make_axioms(list(examples[0]))))

    return result
