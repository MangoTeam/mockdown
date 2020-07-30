from math import sqrt, isclose
from pprint import pprint
from typing import List, TypeVar, Optional, Tuple

import numpy as np
from scipy import special
from scipy import stats
from sympy import Rational, Number, continued_fraction  # type: ignore

from mockdown.constraint import ConstraintKind, IConstraint
from mockdown.learning.math.sequences import q_ball, ext_farey
from mockdown.learning.types import IConstraintLearning, ConstraintCandidate
from mockdown.model import IView

Kind = ConstraintKind

RESOLUTION = 100
EXPECTED_STEPS = 1
ABS_TOL = 0.025

T = TypeVar('T')


def unopt(arg: Optional[T]) -> T:
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

    def learn_multipliers(self, xs: np.ndarray, ys: np.ndarray) -> List[Tuple[Rational, float]]:
        print(f"\nLearning {self._template}")

        xs = xs + np.random.normal(0, 5 / 3, len(xs))
        ys = ys + np.random.normal(0, 5 / 3, len(ys))

        samples = (ys / xs).astype(np.float)
        print(f"  samples: {ys} / {xs} = {samples}")
        mean, median, std = np.mean(samples), np.median(samples), np.std(samples)
        print(f"  mean:    {mean}")
        print(f"  median:  {median}")
        print(f"  std:     {std}")

        cov_mat = np.cov(xs, ys, bias=False)
        print(cov_mat)
        eigvals = np.linalg.eigvals(cov_mat)
        print(eigvals)
        d_score = max(eigvals) / sum(eigvals)  # proportion of variance explained by 1 dimension.

        if np.min(xs) == np.max(xs):
            m, b, r, p = np.inf, np.nan, np.nan, np.nan
        else:
            m, b, r, p, _, = stats.linregress(xs, ys)
        p_score = (1 - p) if (m > 0) and (r is not np.nan) else 0

        balls = [set(q_ball(s, abs_tol=ABS_TOL)) for s in samples]
        candidates = np.array(sorted(set.intersection(*balls)))
        if len(candidates) == 0:
            print("No candidates in intersection of balls.")
            return []
        # min_s = np.min(samples)
        # max_s = np.max(samples)
        # candidates = np.array(
        #     list(sorted(filter(lambda q: min_s < q < max_s, ext_farey(RESOLUTION)))),
        #     dtype=np.object
        # )

        irrs = np.fromiter((irrationality(c) for c in candidates), dtype=np.int)
        max_irr = np.max(irrs)
        min_irr = np.min(irrs)
        n = max_irr - min_irr

        # TODO: WHY IS THE RAT_SCORE SO VOLATILE?!
        if max_irr == min_irr:
            # Handle the degenerate noiseless case.
            # todo: is this needed if we use beta = 1 + (res - exp)?
            print("degenerate")
            rat_scores = stats.rv_discrete(values=([0], [1])).cdf(irrs - min_irr)
        else:
            alpha = 1 + EXPECTED_STEPS
            beta = 1 + (n - EXPECTED_STEPS)
            rat_scores = 1 - stats.betabinom(n, alpha, beta).cdf(irrs)

        if std != 0:
            err_scores = 1 - np.abs(special.erf((candidates.astype(np.float) - mean) / (sqrt(2) * std)))
        else:
            err_scores = (candidates == mean).astype(np.float)

        print("Scores:")
        print(f"  Dim: {d_score}")
        print(f"  P:   {p_score}")
        print(f"  Rat: {rat_scores}")
        print(f"  Err: {err_scores}")
        scores = d_score * p_score * rat_scores * err_scores

        return list(zip(candidates, scores))

    def learn_constraints(self) -> List[Tuple[IConstraint, int]]:
        template = self._template
        kind = template.kind
        examples = self._examples

        if kind.is_mul_only_form:
            xs = np.array([
                unopt(s.find_anchor(unopt(template.x_id))).value
                for s in examples]
            ).astype(np.float)
            ys = np.array([
                unopt(s.find_anchor(template.y_id)).value
                for s in examples]
            ).astype(np.float)

            # Compute observed sample a-values.
            # These might be rationals, or reals. The rest of the process is agnostic.
            a_candidates = self.learn_multipliers(xs, ys)
            candidates = [ConstraintCandidate(template.subst(a=a), score) for (a, score) in a_candidates if not isclose(score, 0, abs_tol=0.01)]
            print("Candidates:")
            pprint(candidates, indent=2)
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
            constraint_set = list(filter(lambda sc: sc.score > 0.5, sorted(scored_constraints, key=lambda sc: sc.score, reverse=True)))
            constraint_sets.append(constraint_set)

        # with Pool(1) as pool:
        #     def run_task(task: RobustLearningTask) -> List[Tuple[IConstraint, int]]:
        #         scored_constraints = task.learn_constraints()
        #         return list(sorted(scored_constraints, key=lambda sc: sc[1], reverse=True))[:self._top_k]
        #
        #     result = pool.map_async(methodcaller('learn_constraints'), tasks).get(timeout=30)
        #     print(result)

        return constraint_sets


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
