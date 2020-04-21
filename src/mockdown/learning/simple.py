import math
import operator
from collections import defaultdict
from dataclasses import replace
from fractions import Fraction
from pprint import pprint
from typing import DefaultDict, Dict, List, Optional, Sequence

from mockdown.constraint import ConstraintKind, IConstraint
from mockdown.constraint.constraint import ConstantConstraint, LinearConstraint
from mockdown.constraint.typing import IComparisonOp
from mockdown.model import IView

Kind = ConstraintKind

DEFAULT_TOLERANCE = 0.01  # maximum difference of 1%
MAX_DENOMINATOR = 1000


class _ConstraintFalsified(Exception):
    def __init__(self, constraint: IConstraint):
        self.constraint = constraint


class SimpleConstraintLearning:
    """
    This class emulates the old learning method.

    The one difference is that it rationalizes its output.
    """

    def __init__(self,
                 templates: Sequence[IConstraint],
                 samples: Sequence[IView[float]],
                 tolerance: float = DEFAULT_TOLERANCE,
                 max_denominator: int = MAX_DENOMINATOR):
        self._templates = templates
        self._samples = samples
        self._tolerance = tolerance
        self._max_denominator = max_denominator

    def learn(self) -> Sequence[IConstraint]:
        # Constants are learned as floats and then rationalized.
        constants: Dict[IConstraint, Dict[str, float]] = {}
        sample_counts: DefaultDict[IConstraint, int] = defaultdict(lambda: 0)
        falsified: DefaultDict[IConstraint, bool] = defaultdict(lambda: False)

        def widen_bound(op: IComparisonOp[float], old: float, new: float) -> float:
            if op == operator.le:
                return max(old, new)
            elif op == operator.ge:
                return min(old, new)
            else:
                raise Exception("unsupported operator")

        for i, sample in enumerate(self._samples):
            for template in self._templates:
                if falsified[template]:
                    continue

                try:
                    x = sample.find_anchor(template.x_id) if template.x_id else None
                    y = sample.find_anchor(template.y_id)
                    assert y is not None, f"Could not find anchor f{template.y_id} in sample #{i}"
                    if template.kind in {Kind.POS_LTRB_OFFSET, Kind.SIZE_OFFSET}:
                        assert x is not None
                        a = 1.0
                        b = y.value - x.value

                        if sample_counts[template] > 0:
                            old_b = constants[template]['b']
                            b = widen_bound(template.op, old=old_b, new=b)

                        constants[template] = {'a': a, 'b': b}
                    elif template.kind is Kind.SIZE_CONSTANT:
                        assert x is None
                        a = 0.0
                        b = y.value

                        if sample_counts[template] > 0:
                            old_b = constants[template]['b']
                            b = widen_bound(template.op, old=old_b, new=b)

                        constants[template] = {'a': a, 'b': b}
                    elif template.kind in {Kind.SIZE_RATIO, Kind.SIZE_ASPECT_RATIO}:
                        assert x is not None
                        a = y.value / x.value
                        b = 0.0

                        if sample_counts[template] > 0:
                            old_a = constants[template]['a']

                            if template.op == operator.eq:
                                if not math.isclose(old_a, a, rel_tol=self._tolerance):
                                    raise _ConstraintFalsified(template)
                                # otherwise leave the original value.
                            else:
                                a = widen_bound(template.op, old=old_a, new=a)

                        constants[template] = {'a': a, 'b': b}
                    else:
                        raise Exception(f"Unsupported constraint kind: {template.kind}.")
                except _ConstraintFalsified as e:
                    # todo, better logging and more informative error
                    print(f"Equality constraint template falsified: {e.constraint}")
                    falsified[template] = True
                    continue

                sample_counts[template] += 1

        constraints: List[IConstraint] = []
        for template in self._templates:
            values = constants[template]

            constraint: Optional[IConstraint] = None
            if isinstance(template, LinearConstraint):
                a = Fraction(values['a']).limit_denominator(self._max_denominator)
                b = Fraction(values['b']).limit_denominator(self._max_denominator)
                constraint = replace(template,
                                     a=a, b=b,
                                     sample_count=sample_counts[template])
                assert constraint is not None
                constraints.append(constraint)
            elif isinstance(template, ConstantConstraint):
                b = Fraction(values['b']).limit_denominator(self._max_denominator)
                constraint = replace(template,
                                     b=b,
                                     sample_count=sample_counts[template])
                assert constraint is not None
                constraints.append(constraint)
            else:
                raise Exception("Unsupported IConstraint implementation.")

        pprint(constraints)
        return constraints
