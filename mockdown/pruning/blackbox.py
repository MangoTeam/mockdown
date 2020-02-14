from typing import List, AbstractSet

import z3

from mockdown.model.bounds import SizeBounds
from mockdown.pruning.typing import PruningMethod
from mockdown.model import IView
from mockdown.model.conformance import Conformance
from mockdown.model.constraint import *

class BlackBoxPruner(PruningMethod):

    def __init__(self, examples: List[IView], bounds: SizeBounds):

        heights = [v.height for v in examples]
        widths = [v.width for v in examples]

        min_w = bounds.min_w or min(widths)
        max_w = bounds.max_w or max(widths)
        min_h = bounds.min_h or min(heights)
        max_h = bounds.max_h or max(heights)

        self.min_conf = Conformance(min_w, min_h, 0,0)
        self.max_conf = Conformance(max_w, max_h, 0,0)

        # print('min conf', self.min_conf)
        # print('max conf', self.max_conf)

        assert len(examples) > 0, "Pruner requires non-empty training examples"

        self.example = examples[0]

        self.top_width = self.example.width_anchor
        self.top_height = self.example.height_anchor
        self.top_x = self.example.left_anchor
        self.top_y = self.example.top_anchor

        

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

    # return a map from asserted layout axioms to explanatory strings
    def addLayoutAxioms(self, solver: z3.Optimize, confIdx: int):

        output = {}

        for box in self.example:
            w, h = box.width_anchor.to_z3_var(confIdx), box.height_anchor.to_z3_var(confIdx)
            l, r = box.left_anchor.to_z3_var(confIdx), box.right_anchor.to_z3_var(confIdx)
            t, b = box.top_anchor.to_z3_var(confIdx), box.bottom_anchor.to_z3_var(confIdx)
            widthAx = w == (r - l)
            heightAx = h == (b - t)

            # print('adding axioms:', widthAx, heightAx, w>=0, h >= 0)
            solver.assert_and_track(widthAx, "width_ax_%d" % confIdx)
            output["width_ax_%d" % confIdx] = "%s = (%s - %s)" % (box.width_anchor.name, box.left_anchor.name, box.right_anchor.name)
            solver.assert_and_track(heightAx, "height_ax_%d" % confIdx) 
            output["height_ax_%d" % confIdx] = "%s = (%s - %s)" % (box.height_anchor.name, box.bottom_anchor.name, box.top_anchor.name)
            # , heightAx
            solver.assert_and_track(w >= 0, "pos_w_%d" % confIdx) 
            solver.assert_and_track(h >= 0, "pos_w_%d" % confIdx) 
            output["pos_w_%d" % confIdx] = "%s >= 0" % box.width_anchor.name
            output["pos_h_%d" % confIdx] = "%s >= 0" % box.height_anchor.name

        return output

    def checkSanity(self, constraints: List[IConstraint]):
        
        confs = self.genExtraConformances()

        print('checking constraints for sanity:', [x.shortStr() for x in constraints])

        for confidx, conf in enumerate(confs):
            solver = z3.Optimize()
            self.addConfDims(solver, conf, confidx)
            self.addLayoutAxioms(solver, confidx)
            # solver.add
            for c in constraints:
                solver.add(c.to_z3_expr(confidx))

            m = solver.model()
            chk = solver.check()

            print('result for', conf)
            print(str(chk))

        
    def isWhole(self, c: IConstraint):
        steps = [0.05 * x for x in range(20)]
        bestDiff = min([abs(s - c.a) for s in steps])
        return bestDiff <= 0.01

    def makePairs(self, constraints: List[IConstraint]):
        return [(c, cp) for c in constraints for cp in constraints if c.fuzzyEq(cp) and c.op != cp.op]



    def buildBiases(self, constraints: List[IConstraint]):
        default = {c: 1 for c in constraints}

        pairs = self.makePairs(constraints)
        # print([(x.shortStr(), y.shortStr()) for (x,y) in pairs][0])


        # reward specific constraints
        for c in constraints:
            score = 10
            # aspect ratios and size constraints are specific the more samples behind them
            if isinstance(c, AspectRatioSizeConstraint):
                # print(c, c.is_falsified)
                score = 1 if c.is_falsified else 100 * c.sample_count
            elif isinstance(c, RelativeSizeConstraint):
                # and doubly specific when the constants are nice
                if self.isWhole(c):
                    score = 1000 * c.sample_count
                else:
                    score = 100 * c.sample_count
            # positions are specific if they're paired and the pairs are close together
            elif isinstance(c, PositionConstraint):
                score = 1000
                # for simplicity we update pairs after this loop
            
            # if (isinstance(c, ))
            if c.is_falsified:
                score = 1 # discard!
            default[c] = score

        for (l, r) in pairs:
            if isinstance(l, PositionConstraint):
                assert isinstance(r, PositionConstraint)

                diff = l.b + r.b
                # map > 500 => 10
                # 0 => 10000
                # everything else linearly
                upper = 500
                lower = 0
                if diff > upper:
                    score = 10
                else:
                    # a * upper + b = 10
                    # a * 0 +  b = 10000
                    # b = 10000, a  = -9990/upper
                    score = (-9990)/upper * diff + 10000
                    default[l] = score
                    default[r] = score
            
        return default

    def addConfDims(self, solver: z3.Optimize, conf: Conformance, confIdx: int):
        output = {}

        top_x_v = self.top_x.to_z3_var(confIdx)
        top_y_v = self.top_y.to_z3_var(confIdx)
        top_w_v = self.top_width.to_z3_var(confIdx)
        top_h_v = self.top_height.to_z3_var(confIdx)
        
        solver.assert_and_track(top_w_v == conf.width, "top_w_%d" % conf.width)
        solver.assert_and_track(top_h_v == conf.height, "top_h_%d" % conf.height)
        solver.assert_and_track(top_x_v == conf.x, "top_x_%d" % conf.x)
        solver.assert_and_track(top_y_v == conf.y, "top_y_%d" % conf.y)

        output["top_w_%d" % conf.width] = str(top_w_v) + " = " + str(conf.width)
        output["top_h_%d" % conf.height] = str(top_h_v) + " = " + str(conf.height)

        return output

    def __call__(self, constraints: List[IConstraint]):

        # build up all of the constraints as Z3 objects

        idents = set()
        solver = z3.Optimize()

        namesMap = {}
        biases = self.buildBiases(constraints)
        axiomMap = {}

        confs = self.genExtraConformances()

        for confIdx, conf in enumerate(confs):

            axiomMap = {**axiomMap, **self.addConfDims(solver, conf, confIdx)}
            axiomMap = {**axiomMap, **self.addLayoutAxioms(solver, confIdx)}
            
        
        for constrIdx, constr in enumerate(constraints):
            cvname = "constr_var" + str(constrIdx)
            cvar = z3.Bool(cvname)

            namesMap[cvname] = constr
            solver.add_soft(cvar, biases[constr])

            for confIdx in range(len(confs)):
                solver.add(z3.Implies(cvar, constr.to_z3_expr(confIdx)))

                # solver.assert_and_track(, cvar)
                

        sanitys = []
        for constrIdx, constr in enumerate(constraints):
            cvname = "constr_var" + str(constrIdx)
            cvar = z3.Bool(cvname)

            # captures = ['box0.center_x', 'box0.width']
            captures = ['box0.height']
            types = (AspectRatioSizeConstraint)

            if str(constr.y) in captures and not isinstance(constr, types):
                sanitys.append(constr)
        # self.checkSanity(sanitys)



        chk = solver.check()
        if (str(chk) is 'sat'):

            constrValues = [v for v in solver.model().decls() if v.name() in namesMap]
            output = [namesMap[v.name()] for v in constrValues if solver.model().get_interp(v)]
            pruned = [c.shortStr() for c in constraints if c not in output]
            print('output: ', [o.shortStr() for o in output])
            print('pruned: ', pruned)
            
            return output
        elif (str(chk) is 'unsat'):
            # allConstraints = {**namesMap, **axiomMap}
            incompat = [axiomMap[str(v)] for v in solver.unsat_core() if str(v) in axiomMap] + [namesMap[str(c)].shortStr() for c in solver.unsat_core() if str(c) in namesMap]
            print('unsat!')
            print('core: ', solver.unsat_core())
            print('pretty: ', incompat)
            # print('values: ', [solver.model().get_interp(c.y) for c in incompat])
        else:
            print('unknown: ', chk)

        # print("constraints:")
        # print(namesMap)

        return constraints


