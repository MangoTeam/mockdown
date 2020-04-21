from collections import defaultdict
from dataclasses import replace
from fractions import Fraction
from typing import DefaultDict, Dict, Generic, List, Optional, Sequence

from mockdown.constraint import ConstraintKind, IConstraint
from mockdown.constraint.constraint import ConstantConstraint, LinearConstraint

from mockdown.model import IView
from mockdown.typing import NT, unreachable

Kind = ConstraintKind

DEFAULT_TOLERANCE = 0.01  # maximum difference of 1%
MAX_DENOMINATOR = 1000


class DaikonStyleConstraintLearning:
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
        sample_counts: DefaultDict[IConstraint, int] = defaultdict(default_factory=lambda: 0)

        for i, sample in enumerate(self._samples):
            for template in self._templates:
                values = {}
                if template.kind is Kind.POS_LTRB_OFFSET:
                    values['a'] = 1.0
                    # todo
                    pass
                elif template.kind is Kind.SIZE_OFFSET:
                    pass
                elif template.kind is Kind.SIZE_CONSTANT:
                    pass
                elif template.kind is Kind.SIZE_RATIO:
                    pass
                elif template.kind is Kind.SIZE_ASPECT_RATIO:
                    pass
                else:
                    raise Exception(f"Unsupported constraint kind: {template.kind}.")

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
            elif isinstance(template, ConstantConstraint):
                b = Fraction(values['b']).limit_denominator(self._max_denominator)
                constraint = replace(template,
                                     b=b,
                                     sample_count=sample_counts[template])
            else:
                raise Exception("Unsupported IConstraint implementation.")

            assert constraint is not None
            constraints.append(constraint)

        return constraints



