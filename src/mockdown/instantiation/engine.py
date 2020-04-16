from typing import Any, Sequence, Set

from .logic import valid_constraints
from .typing import IConstraintInstantiator
from .visibility import visible_pairs
from ..constraint import IConstraint
from ..model import IView
from ..typing import NT


class VisibilityConstraintInstantiator(IConstraintInstantiator[Any]):
    def instantiate(self, examples: Sequence[IView[NT]]) -> Sequence[IConstraint]:
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

        constraint_sets = {
            set(valid_constraints(examples[i], anchor_pair_sets[i]))
            for i
            in range(len(examples))
        }

        all_constraints: Set[IConstraint] = set()
        for constraint_set in constraint_sets:
            all_constraints = all_constraints.union(constraint_set)

        return list(all_constraints)
