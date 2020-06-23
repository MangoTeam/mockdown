import json
from typing import TextIO

import sympy as sym

from mockdown.instantiation import VisibilityConstraintInstantiator
from mockdown.learning.simple import SimpleConstraintLearning
from mockdown.model import ViewLoader
from mockdown.pruning import BlackBoxPruner, HierarchicalPruner


def run(input_io: TextIO, numeric_type: str, pruning_method: str) -> dict:
    """
    This command's guts are pulled out here so they can be called from Python
    directly, as well as from the CLI.

    It is in its own file to prevent import cycles between cli and app!
    """
    input_data = json.load(input_io)

    examples_data = input_data["examples"]
    bounds = input_data.get('bounds', {})

    # Note: sym.Number _should_ generally "do the right thing"...
    number_factory = {
        'N': sym.Number,
        'R': sym.Float,
        'Q': sym.Rational,
        'Z': sym.Integer
    }[numeric_type]

    pruner_factory = {
        'none': lambda x, y: (lambda cns: cns),
        'baseline': BlackBoxPruner,
        'hierarchical': HierarchicalPruner,
    }[pruning_method]

    loader = ViewLoader(number_factory=sym.Number)
    instantiator = VisibilityConstraintInstantiator()

    # 1. Load Examples

    examples = [loader.load_dict(ex_data) for ex_data in examples_data]

    # 2. Instantiate Templates
    templates = instantiator.instantiate(examples)

    # 3. Learn Constants.
    learning = SimpleConstraintLearning(samples=examples, templates=templates)
    constraints = [candidate.constraint
                   for candidates in learning.learn()
                   for candidate in candidates]

    # 4. Pruning.
    prune = pruner_factory(examples, bounds)
    pruned_constraints = prune(constraints)

    return [cn.to_dict() for cn in pruned_constraints]
