from .typing import Priority

ISCLOSE_TOLERANCE = 0.01  # maximum difference of 1%
PRIORITY_REQUIRED: Priority = (1000, 1000, 1000)
PRIORITY_STRONG: Priority = (1, 0, 0)
PRIORITY_MEDIUM: Priority = (0, 1, 0)
PRIORITY_WEAK: Priority = (0, 0, 1)