from dataclasses import dataclass


@dataclass(frozen=True)
class Conformance:
    # TODO: these should be ints! – Dylan
    width: float
    height: float

    # TODO: do we need x/y in top-level conformances? right now they're always 0
    x: int
    y: int
