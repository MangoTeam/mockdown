from typing import Callable, List, Tuple

from mockdown.model import IView
from mockdown.model.bounds import SizeBounds
from mockdown.model.constraint import IConstraint

PruningMethod = Callable[[List[IConstraint]], List[IConstraint]]
PruningMethodFactory = Callable[[List[IView], SizeBounds], PruningMethod]