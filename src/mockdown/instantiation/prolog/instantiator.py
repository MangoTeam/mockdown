from typing import Sequence, Set

from mockdown.constraint import IConstraint
# from mockdown.instantiation.normalization import normalize_multiplier
from mockdown.instantiation.types import IConstraintInstantiator
from mockdown.instantiation.prolog.logic import valid_constraints
from mockdown.instantiation.visibility import visible_pairs

from mockdown.model import IView
from mockdown.types import NT


class PrologConstraintInstantiator(IConstraintInstantiator[NT]):
    def __init__(self, examples: Sequence[IView[NT]]):
        super().__init__(examples)
        self.examples = examples

    def detect_visibilities(self):
        examples = self.examples

        edge_pair_sets = [
            visible_pairs(example, deep=True)
            for example
            in examples
        ]

        anchor_pair_sets = [
            [(e1.anchor, e2.anchor) for (e1, e2) in edge_pair_set]
            for edge_pair_set
            in edge_pair_sets
        ]

        return anchor_pair_sets

    def instantiate(self) -> Sequence[IConstraint]:
        examples = self.examples
        anchor_pair_sets = self.detect_visibilities()

        constraint_sets = {
            valid_constraints(examples[i], anchor_pair_sets[i])
            for i
            in range(len(examples))
        }

        all_constraints: Set[IConstraint] = set()
        for constraint_set in constraint_sets:
            all_constraints = all_constraints.union(constraint_set)

        # todo: is this necessary..?
        # return list(sorted(map(normalize_multiplier, all_constraints)))
        return list(all_constraints)


