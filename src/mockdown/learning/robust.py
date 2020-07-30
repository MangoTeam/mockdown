from math import erf, sqrt, isclose
from pprint import pprint
from statistics import stdev, fmean
from typing import List, TypeVar, Optional, Tuple

from sympy import Rational, Number, continued_fraction, N  # type: ignore
from sympy.stats import BetaBinomial, FiniteRV, cdf, density  # type: ignore

from mockdown.constraint import ConstraintKind, IConstraint
from mockdown.learning.math.sequences import q_ball
from mockdown.learning.typing import IConstraintLearning, ConstraintCandidate
from mockdown.model import IView

Kind = ConstraintKind

MAX_DENOMINATOR = 100
EXPECTED_STEPS = 1
REL_TOL = 0.01

T = TypeVar('T')


def unoptional(arg: Optional[T]) -> T:
    assert arg is not None
    return arg


def irrationality(q: Rational) -> int:
    return sum([int(x) for x in continued_fraction(q)])


class RobustLearningTask:
    """
    Learns a single template given some set of samples.
    Many of these are used at once for learning invariants for an entire layout.
    """
    _template: IConstraint
    _examples: List[IView[Number]]

    def __init__(self,
                 template: IConstraint,
                 samples: List[IView[Number]]):
        self._template = template
        self._examples = samples

    def learn_multipliers(self, samples: List[Number]) -> List[Tuple[Rational, float]]:
        print(f"\nLearning {self._template}")

        samples_f = [float(s) for s in samples]
        print(f"  samples: {samples_f}")
        mean, std = fmean(samples_f), stdev(samples_f)
        print(f"  mean:    {mean}")
        print(f"  std:     {std}")

        balls = [set(q_ball(s, rel_tol=REL_TOL)) for s in samples_f]
        candidates = list(sorted(set.union(*balls)))

        irrs = {c: irrationality(c) for c in candidates}

        max_irr = max(irrs.values())
        min_irr = min(irrs.values())
        n = max_irr - min_irr

        if n == 0:
            # Handle the degenerate noiseless case.
            score_dist = FiniteRV('RationalityPrior', {0: 1})
        else:
            alpha = 1 + EXPECTED_STEPS
            beta = 1 + (n - EXPECTED_STEPS)
            score_dist = BetaBinomial('RationalityPrior', n, alpha, beta)

        def r_score_fn(q) -> float:
            return density(score_dist)[q]
        r_scores = [N(r_score_fn(irrs[c] - min_irr)) for c in candidates]

        def e_score_fn(q) -> float:
            # Handle the degenerate noiseless case.
            if std == 0:
                return 1 if q == mean else 0
            return 1 - abs(erf((q - mean) / (sqrt(2) * std)))
        e_scores = [e_score_fn(c) for c in candidates]
        scores = [r * e for (r, e) in zip(r_scores, e_scores)]

        return list(zip(candidates, e_scores))

    def learn_constraints(self) -> List[Tuple[IConstraint, int]]:
        template = self._template
        kind = template.kind
        examples = self._examples

        if kind.is_mul_only_form:
            xs = [unoptional(sample.find_anchor(unoptional(template.x_id))) for sample in examples]
            ys = [unoptional(sample.find_anchor(template.y_id)) for sample in examples]

            # Compute observed sample a-values.
            # These might be rationals, or reals. The rest of the process is agnostic.
            a_samples = [y.value / x.value for (x, y) in zip(xs, ys)]
            a_candidates = self.learn_multipliers(a_samples)
            candidates = [(template.subst(a=a), score) for (a, score) in a_candidates]
            print("Candidates:")
            pprint(candidates)
            return candidates
        else:
            return []

    # def to_constraints(self) -> List[IConstraint]:
    #     raise NotImplementedError


class RobustLearning(IConstraintLearning):
    """
    This class emulates the old learning method.

    The one difference is that it rationalizes its output.
    """
    _templates: List[IConstraint]
    _examples: List[IView[Number]]
    _top_k: int

    def __init__(self,
                 templates: List[IConstraint],
                 samples: List[IView[Number]],
                 top_k: int = 3):
        """
        :param confidence_threshold: cutoff for returned constraints, 0-1.
        """
        self._templates = templates
        self._examples = samples
        self._top_k = 3

    def learn(self) -> List[List[ConstraintCandidate]]:
        tasks = [RobustLearningTask(tpl, self._examples) for tpl in self._templates]

        constraint_sets = []

        for task in tasks:
            scored_constraints = task.learn_constraints()
            constraint_sets.append(sorted(scored_constraints, key=lambda sc: sc[1], reverse=True)[:self._top_k])

        # with Pool(1) as pool:
        #     def run_task(task: RobustLearningTask) -> List[Tuple[IConstraint, int]]:
        #         scored_constraints = task.learn_constraints()
        #         return list(sorted(scored_constraints, key=lambda sc: sc[1], reverse=True))[:self._top_k]
        #
        #     result = pool.map_async(methodcaller('learn_constraints'), tasks).get(timeout=30)
        #     print(result)

        return []


if __name__ == '__main__':
    print("hello")
#     golden = 4.0 / 7.0
#     perturbs = []
#
#     num_perturbs = 50
#     max_depth = 20
#     pct_noise = 0.1
#
#     for i in range(num_perturbs):
#         # precision = random.randint(1, 10)
#         noise = random.uniform(-pct_noise * golden, pct_noise * golden)
#
#         # perturb = float(f"{golden:.{precision}f}") + noise
#         perturb = golden + noise
#         perturbs.append(perturb)
#
#     print(*(['depth'] + perturbs), sep='\t')
#
#     cand_sets = [candidate_rationals(p) for p in perturbs]
#
#     data = [[None] * num_perturbs for _ in range(max_depth)]
#
#     for d in range(1, max_depth):
#         for i, cands in enumerate(cand_sets):
#             try:
#                 cand = next(cand for cand in cands if cand.depth == d)
#                 data[d][i] = cand.value
#             except StopIteration:
#                 continue
#
#     for d in range(max_depth):
#         print(*([d] + data[d]), sep='\t')
