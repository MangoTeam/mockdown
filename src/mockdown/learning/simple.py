import math
import operator
from collections import defaultdict
from dataclasses import replace, dataclass
from typing import DefaultDict, Dict, List, Optional, Sequence

import sympy as sym

from mockdown.constraint import ConstraintKind, IConstraint
from mockdown.constraint.constraint import ConstantConstraint, LinearConstraint
from mockdown.learning.errors import ConstraintFalsified
from mockdown.learning.types import IConstraintLearning, ConstraintCandidate
from mockdown.learning.util import widen_bound
from mockdown.model import IView
from more_itertools import first_true

Kind = ConstraintKind

DEFAULT_TOLERANCE = 0.01  # maximum difference of 1%
MAX_DENOMINATOR = 100


@dataclass(frozen=True)
class SimpleLearningConfig():
    tolerance: float = DEFAULT_TOLERANCE
    max_denominator: int = MAX_DENOMINATOR


class SimpleLearning(IConstraintLearning):
    """
    This class emulates the old learning method.

    The one difference is that it rationalizes its output.
    """

    def __init__(self,
                 templates: List[IConstraint],
                 samples: List[IView[sym.Number]],
                 config: Optional[SimpleLearningConfig] = None):
        self._templates = templates
        self._examples = samples

        if not config:
            config = SimpleLearningConfig()

        self._tolerance = config.tolerance
        self._max_denominator = config.max_denominator

    def learn(self) -> List[List[ConstraintCandidate]]:
        # Constants are learned as floats and then rationalized.
        constants: Dict[IConstraint, Dict[str, sym.Number]] = {}
        sample_counts: DefaultDict[IConstraint, int] = defaultdict(lambda: 0)
        falsified: DefaultDict[IConstraint, bool] = defaultdict(lambda: False)

        for i, sample in enumerate(self._examples):
            for template in self._templates:
                if falsified[template]:
                    continue

                try:
                    x = sample.find_anchor(template.x_id) if template.x_id else None
                    y = sample.find_anchor(template.y_id)
                    assert y is not None, f"Could not find anchor f{template.y_id} in sample #{i}"
                    if template.kind in {Kind.POS_LTRB_OFFSET, Kind.SIZE_OFFSET}:
                        assert x is not None
                        a = sym.Number(1.0)
                        b = y.value - x.value

                        if sample_counts[template] > 0:
                            old_b = constants[template]['b']

                            if template.op == operator.eq:
                                if not math.isclose(old_b, b, rel_tol=self._tolerance):
                                    raise ConstraintFalsified(template)
                                # otherwise leave the original value.
                            else:
                                b = widen_bound(template.op, old=old_b, new=b)

                        constants[template] = {'a': a, 'b': b}
                    elif template.kind is Kind.SIZE_CONSTANT:
                        assert x is None
                        a = sym.Number(0.0)
                        b = y.value

                        if sample_counts[template] > 0:
                            old_b = constants[template]['b']

                            if template.op == operator.eq:
                                if not math.isclose(old_b, b, rel_tol=self._tolerance):
                                    raise ConstraintFalsified(template)
                                # otherwise leave the original value.
                            else:
                                b = widen_bound(template.op, old=old_b, new=b)

                        constants[template] = {'a': a, 'b': b}
                    elif template.kind in {Kind.SIZE_RATIO, Kind.SIZE_ASPECT_RATIO}:
                        assert x is not None
                        a = y.value / x.value
                        b = sym.Number(0.0)

                        if sample_counts[template] > 0:
                            old_a = constants[template]['a']

                            if template.op == operator.eq:
                                if not math.isclose(old_a, a, rel_tol=self._tolerance):
                                    raise ConstraintFalsified(template)
                                # otherwise leave the original value.
                            else:
                                a = widen_bound(template.op, old=old_a, new=a)

                        constants[template] = {'a': a, 'b': b}
                    else:
                        raise Exception(f"Unsupported constraint kind: {template.kind}.")
                except ConstraintFalsified as e:
                    # todo, better logging and more informative error
                    print(f"Equality constraint template falsified: {e.constraint}")
                    falsified[template] = True
                    continue

                sample_counts[template] += 1

        constraints: List[IConstraint] = []
        for template in self._templates:
            values = constants[template]

            if falsified[template]:
                continue

            constraint: Optional[IConstraint] = None
            if isinstance(template, LinearConstraint):
                a_frac = sym.Rational(values['a']).limit_denominator(self._max_denominator)
                b_frac = sym.Rational(values['b']).limit_denominator(self._max_denominator)
                constraint = replace(template,
                                     a=a_frac,
                                     b=b_frac,
                                     sample_count=sample_counts[template], )
                constraints.append(constraint)
            elif isinstance(template, ConstantConstraint):
                b_frac = sym.Rational(values['b']).limit_denominator(self._max_denominator)
                constraint = replace(template,
                                     b=b_frac,
                                     sample_count=sample_counts[template])
                constraints.append(constraint)
            else:
                raise Exception("Unsupported IConstraint implementation.")

        return [[ConstraintCandidate(constraint, 0)] for constraint in constraints]



class HeuristicLearning(SimpleLearning):
    def __init__(self,
                 templates: List[IConstraint],
                 samples: List[IView[sym.Number]],
                 config: Optional[SimpleLearningConfig] = None):
        super().__init__(templates, samples, config)


    def build_biases(self, constraints: List[IConstraint]) -> Dict[IConstraint, float]:
        scores = {c: 1.0 for c in constraints}

        # reward specific constraints
        for c in constraints:
            score = 1.0
            # aspect ratios and size constraint are specific the more samples behind them
            if c.kind is ConstraintKind.SIZE_ASPECT_RATIO:
                score = 1 if c.is_falsified else 100
            elif c.kind is ConstraintKind.SIZE_RATIO:
                score = 100
            elif c.kind.is_position_kind or c.kind is ConstraintKind.SIZE_OFFSET:

                if c.op == operator.eq:

                    diff = abs(c.b)
                    # map > 100 => 10
                    # 0 => 1000
                    # everything else linearly
                    upper = 25
                    lower = 0
                    if diff > upper:
                        score = 10
                    else:
                        score = (-990) / upper * diff + 1000
                else:
                    score = 10  # penalize leq/geq

            elif c.kind is ConstraintKind.SIZE_CONSTANT:

                if c.op == operator.eq:
                    score = 1000
                else:
                    score = 10  # penalize leq/geq

            scores[c] = int(score * self.whole_score(c)) 
        return scores

    def whole_score(self, c: IConstraint) -> int:
        score = 1
        if c.x_id:
            if c.a.p < 25:
                score *= 10
            if c.a.p < 10:
                score *= 10
            if c.a.p > 100:
                # we probably don't want this...
                return 1
        if c.b.p < 25:
            score *= 10
        if c.b.p < 10:
            score *= 10
        if c.b.p > 100:
            # we probably don't want this...
            return score
        return score

    def filter_constraints(self, constraints: List[IConstraint], elim_uneq: bool = True) -> List[IConstraint]:
        constraints = [c for c in constraints if c.kind != ConstraintKind.SIZE_ASPECT_RATIO]
        constraints = self.combine_bounds(constraints)
        if elim_uneq: constraints = list(filter(lambda c: c.op == operator.eq, constraints))
        return constraints

    def combine_bounds(self, constraints: List[IConstraint]) -> List[IConstraint]:
        output: Set[IConstraint] = set()
        for c in constraints:
            other = first_true(iterable=constraints, pred=lambda t: anchor_equiv(c, t) and c.op != t.op, default=c)
            if other != c and abs(other.b - c.b) < 5:
                output.add(replace(c, op=operator.eq, b=(other.b + c.b) / 2, priority=PRIORITY_STRONG))
            else:
                output.add(c)
        return list(output)
    
    def learn(self):
        cands = super().learn()
        constraints = self.filter_constraints([x.constraint for y in cands for x in y])
        biases = self.build_biases(constraints)
        
        return [[ConstraintCandidate(c, biases[c])] for c in constraints]


def anchor_equiv(c1: IConstraint, c2: IConstraint) -> bool:
    """
    Equivalence modulo anchors.
    """
    return c1.y_id == c2.y_id and c1.x_id == c2.x_id