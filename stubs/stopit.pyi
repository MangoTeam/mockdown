from typing import TypeVar, Callable, overload, Optional

# Note, the correct way to type this would be to use ParamSpec, but it is Python 3.10 only.
# See: https://www.python.org/dev/peps/pep-0612/#paramspec-variables
#
# What we do instead is use ... which is a dirty but necessary hack according to the BDFL.

R = TypeVar('R')

class threading_timeoutable:
    def __init__(self, default: Optional[int], timeout_param: str): ...

    def __call__(self, f: Callable[..., R]) -> Callable[..., R]: ...

