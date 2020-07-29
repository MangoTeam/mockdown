from dataclasses import dataclass, field
from typing import Sequence, List

import sympy as sym

from mockdown.constraint import ConstraintKind, IConstraint
from mockdown.learning.typing import IConstraintLearning
from mockdown.model import IView

Kind = ConstraintKind

DEFAULT_TOLERANCE = 0.01  # maximum difference of 1%
MAX_DENOMINATOR = 1000


@dataclass
class RobustLearningInvariant:
    template: IConstraint
    samples: List[IView[sym.Number]]



    # def to_constraints(self) -> List[IConstraint]:
    #     raise NotImplementedError


class RobustLearning(IConstraintLearning):
    """
    This class emulates the old learning method.

    The one difference is that it rationalizes its output.
    """

    def __init__(self,
                 templates: Sequence[IConstraint],
                 samples: Sequence[IView[sym.Number]],
                 confidence_threshold: int = 0.95):
        """
        :param confidence_threshold: cutoff for returned constraints, 0-1.
        """
        self._templates = templates
        self._samples = samples
        self._confidence_threshold = confidence_threshold

    def learn(self) -> Sequence[IConstraint]:
        invs = [RobustLearningInvariant(tpl for tpl in self._templates)]


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
