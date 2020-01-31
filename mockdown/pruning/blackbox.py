from typing import List, AbstractSet

import z3

from mockdown.model.bounds import SizeBounds
from mockdown.pruning.typing import PruningMethod
from mockdown.model import IView
from mockdown.model.conformance import Conformance
from mockdown.model.constraint import IConstraint


class BlackBoxPruner(PruningMethod):

    def __init__(self, examples: List[IView], bounds: SizeBounds):

        heights = [v.height for v in examples]
        widths = [v.width for v in examples]

        min_h, max_h = min(heights), max(heights)
        # min_w, max_w = min(widths), max(widths)
        min_w, max_w = bounds.min_w, bounds.max_w

        assert min_w, "Must provide minimum width for blackbox pruning."
        assert max_w, "Must provixe maximum width for blackbox pruning."

        self.min_conf = Conformance(min_w, min_h, 0, 0)
        self.max_conf = Conformance(max_w, max_h, 0, 0)

        # print('min conf', self.min_conf)
        # print('max conf', self.max_conf)

        assert len(examples) > 0, "Pruner requires non-empty training examples"

        self.top_width = examples[0].width_anchor
        self.top_height = examples[0].height_anchor
        self.top_x = examples[0].left_anchor
        self.top_y = examples[0].top_anchor

        self.example = examples[0]

    def genExtraConformances(self) -> AbstractSet[Conformance]:
        # create 10 evenly spaced conformances on the range [min height/width...max height/width]
        extras = set()
        scale = 10
        diff_h = (self.max_conf.height - self.min_conf.height)/(scale * 1.0)
        diff_w = (self.max_conf.width - self.min_conf.width)/(scale * 1.0)

        # print('min/max:', self.max_conf, self.max_conf.width)
        for step in range(0,scale):
            new_c = Conformance(self.min_conf.width + diff_w * step, self.min_conf.height + diff_h * step, 0, 0)
            extras.add(new_c)

        return extras

    # add axioms for width = right - left, width >= 0, height = bottom - top, height >= 0
    # specialized to a particular conformance
    def addLayoutAxioms(self, solver: z3.Optimize, confIdx: int):

        for box in self.example:
            w, h = box.width_anchor.to_z3_var(confIdx), box.height_anchor.to_z3_var(confIdx)
            l, r = box.left_anchor.to_z3_var(confIdx), box.right_anchor.to_z3_var(confIdx)
            t, b = box.top_anchor.to_z3_var(confIdx), box.bottom_anchor.to_z3_var(confIdx)
            widthAx = w == (r - l)
            heightAx = h == (b - t)

            # print('adding axioms:', widthAx, heightAx, w>=0, h >= 0)
            solver.add(widthAx, heightAx)
            solver.add(w >= 0, h >= 0)

        return


    def __call__(self, constraints: List[IConstraint]):

        # build up all of the constraints as Z3 objects

        idents = set()
        solver = z3.Optimize()

        namesMap = {}

        confs = self.genExtraConformances()

        for confIdx, conf in enumerate(confs):
            top_x_v = z3.Real(str(self.top_x.identifier) + "_" + str(confIdx))
            top_y_v = z3.Real(str(self.top_y.identifier) + "_" + str(confIdx))
            top_w_v = z3.Real(str(self.top_width.identifier) + "_" + str(confIdx))
            top_h_v = z3.Real(str(self.top_height.identifier) + "_" + str(confIdx))

            # print('adding top-level constraint', top_w_v, top_w_v == conf.width)

            solver.add(top_x_v == conf.x, top_y_v == conf.y)
            solver.add(top_w_v == conf.width, top_h_v == conf.height)

            self.addLayoutAxioms(solver, confIdx)



        for constrIdx, constr in enumerate(constraints):
            cvname = "constr_var" + str(constrIdx)
            cvar = z3.Bool(cvname)

            namesMap[cvname] = constr
            solver.add_soft(cvar)

            for confIdx in range(len(confs)):
                solver.add(z3.Implies(cvar, constr.to_z3_expr(confIdx)))


        chk = solver.check()
        if (str(chk) is 'sat'):

            constrValues = [v for v in solver.model().decls() if v.name() in namesMap]
            output = [namesMap[v.name()] for v in constrValues if solver.model().get_interp(v)]
            # pruned = [c.shortStr() for c in constraints if c not in output]
            # print('output: ', [o.shortStr() for o in output])
            # print('pruned: ', pruned)

            return output
        elif (str(chk) is 'unsat'):
            print('unsat!')
            print(solver.unsat_core())
        else:
            print('unknown: ', chk)

        # print("constraints:")
        # print(namesMap)

        return constraints