from dataclasses import dataclass
from typing import Optional


@dataclass
class SizeBounds:
    min_w: Optional[int] = None
    min_h: Optional[int] = None
    max_w: Optional[int] = None
    max_h: Optional[int] = None


def get_bounds(json: dict) -> SizeBounds:
    # print('bounds:', json)
    if json is None:
        return SizeBounds()
    else:
        return SizeBounds(
            json.get('min_w', None),
            json.get('min_h', None),
            json.get('max_w', None),
            json.get('max_h', None),
        )