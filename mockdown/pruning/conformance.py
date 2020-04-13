from dataclasses import dataclass


@dataclass(frozen=True)
class Conformance:
    width: int
    height: int

    # TODO: do we need x/y in top-level conformances? right now they're always 0
    x: int
    y: int
