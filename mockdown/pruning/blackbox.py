from typing import List, AbstractSet, Tuple, Dict

import z3
import kiwisolver

from mockdown.model.bounds import SizeBounds, confs_to_bounds
from mockdown.pruning.typing import PruningMethod
from mockdown.model import IView
from mockdown.model.conformance import Conformance
from mockdown.model.constraint import *


def debugSolverValues(solver: z3.Optimize, variables: List[str], fields: List[str], idx: int):
    var_names = [var + '.' + field + "_" + str(idx) for var in variables for field in fields]
    model = solver.model()

    # print('z3 decls:')
    # print(model.decls())
    # print('vars:')
    # print(var_names)

    print('solver values:')
    dec_names = [d.name() for d in model.decls()]
    for vn in var_names:
        if vn in dec_names:
            vn = z3.Real(vn)
            print('%s : %s' % (vn, model.get_interp(vn).as_decimal(15)))
        else:
            print('%s : unconstrained' % vn)

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

        if diff_h == 0 and diff_w == 0:
            # print('optimizing!')
            extras.add(self.max_conf)
            return extras
        
        # print('min/max:', self.max_conf, self.max_conf.width)
        for step in range(0,scale):
            new_c = Conformance(self.min_conf.width + diff_w * step, self.min_conf.height + diff_h * step, 0, 0)
            extras.add(new_c)

        return extras

    # add axioms for width = right - left, width >= 0, height = bottom - top, height >= 0
    # specialized to a particular conformance

    # return a map from asserted layout axioms to explanatory strings
    def addLayoutAxioms(self, solver: z3.Optimize, confIdx: int, linearize: bool = False) -> Dict[str, str]:

        output = {}

        for box in self.example:
            w, h = box.width_anchor.to_z3_var(confIdx, linearize), box.height_anchor.to_z3_var(confIdx, linearize)
            l, r = box.left_anchor.to_z3_var(confIdx, linearize), box.right_anchor.to_z3_var(confIdx, linearize)
            t, b = box.top_anchor.to_z3_var(confIdx, linearize), box.bottom_anchor.to_z3_var(confIdx, linearize)
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

    def addConfDims(self, solver: z3.Optimize, conf: Conformance, confIdx: int, linearize: bool = False):
        output = {}

        top_x_v = self.top_x.to_z3_var(confIdx, linearize)
        top_y_v = self.top_y.to_z3_var(confIdx, linearize)
        top_w_v = self.top_width.to_z3_var(confIdx, linearize)
        top_h_v = self.top_height.to_z3_var(confIdx, linearize)
        
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
        linearize = False

        namesMap = {}
        biases = self.buildBiases(constraints)
        axiomMap = {}

        confs = self.genExtraConformances()

        for confIdx, conf in enumerate(confs):

            axiomMap = {**axiomMap, **self.addConfDims(solver, conf, confIdx, linearize=linearize)}
            axiomMap = {**axiomMap, **self.addLayoutAxioms(solver, confIdx)}
            
        
        for constrIdx, constr in enumerate(constraints):
            cvname = "constr_var" + str(constrIdx)
            cvar = z3.Bool(cvname)

            namesMap[cvname] = constr
            solver.add_soft(cvar, biases[constr])

            for confIdx in range(len(confs)):
                solver.add(z3.Implies(cvar, constr.to_z3_expr(confIdx, linearize)))

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


        # print('z3 expr:')
        with open("debug.smt2", 'w') as debugout:
            print(solver.sexpr(), file=debugout)
            # assert False

        print("solving")
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

class CegisPruner(PruningMethod):

    def __init__(self, examples: List[IView], bounds: SizeBounds):

        heights = [v.height for v in examples]
        widths = [v.width for v in examples]

        min_w = bounds.min_w or min(widths)
        max_w = bounds.max_w or max(widths)
        min_h = bounds.min_h or min(heights)
        max_h = bounds.max_h or max(heights)

        self.min_conf = Conformance(min_w, min_h, 0,0)
        self.max_conf = Conformance(max_w, max_h, 0,0)

        assert len(examples) > 0, "Pruner requires non-empty training examples"

        self.example = examples[0]

        self.top_width = self.example.width_anchor
        self.top_height = self.example.height_anchor
        self.top_x = self.example.left_anchor
        self.top_y = self.example.top_anchor

    # add axioms for width = right - left, width >= 0, height = bottom - top, height >= 0
    # specialized to a particular conformance

    # return a map from asserted layout axioms to explanatory strings
    def addLayoutAxioms(self, solver: z3.Optimize, confIdx: int, linearize: bool = False):

        for box in self.example:
            w, h = box.width_anchor.to_z3_var(confIdx, linearize), box.height_anchor.to_z3_var(confIdx, linearize)
            l, r = box.left_anchor.to_z3_var(confIdx, linearize), box.right_anchor.to_z3_var(confIdx, linearize)
            t, b = box.top_anchor.to_z3_var(confIdx, linearize), box.bottom_anchor.to_z3_var(confIdx, linearize)
            widthAx = w == (r - l)
            heightAx = h == (b - t)

            # print('adding axioms:', widthAx, heightAx, w>=0, h >= 0)
            solver.add(widthAx)
            solver.add(heightAx) 

            solver.add(w >= 0) 
            solver.add(h >= 0) 


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

                default[l] = max(score, default[l])
                default[r] = max(score, default[r])
            
        return default

    def addConfDims(self, solver: z3.Optimize, conf: Conformance, confIdx: int, linearize: bool = False):
        output = {}

        top_x_v = self.top_x.to_z3_var(confIdx, linearize)
        top_y_v = self.top_y.to_z3_var(confIdx, linearize)
        top_w_v = self.top_width.to_z3_var(confIdx, linearize)
        top_h_v = self.top_height.to_z3_var(confIdx, linearize)
        
        solver.assert_and_track(top_w_v == conf.width, "top_w_%d" % conf.width)
        solver.assert_and_track(top_h_v == conf.height, "top_h_%d" % conf.height)
        solver.assert_and_track(top_x_v == conf.x, "top_x_%d" % conf.x)
        solver.assert_and_track(top_y_v == conf.y, "top_y_%d" % conf.y)

        output["top_w_%d" % conf.width] = str(top_w_v) + " = " + str(conf.width)
        output["top_h_%d" % conf.height] = str(top_h_v) + " = " + str(conf.height)

        return output

    def addVerifDims(self, solver: z3.Solver, linearize: bool = False):

        confIdx = 0

        top_x_v = self.top_x.to_z3_var(confIdx, linearize)
        top_y_v = self.top_y.to_z3_var(confIdx, linearize)
        top_w_v = self.top_width.to_z3_var(confIdx, linearize)
        top_h_v = self.top_height.to_z3_var(confIdx, linearize)
        
        solver.add(top_w_v >= self.min_conf.width)
        solver.add(top_h_v >= self.min_conf.height)
        solver.add(top_w_v <= self.max_conf.width)
        solver.add(top_h_v <= self.max_conf.height)

        solver.add(top_x_v >= self.min_conf.x)
        solver.add(top_y_v >= self.min_conf.y)
        solver.add(top_x_v <= self.max_conf.x)
        solver.add(top_y_v <= self.max_conf.y)

    def getVerifDims(self, solver: z3.Solver):

        confIdx = 0
        linearize = False

        top_x_v = self.top_x.to_z3_var(confIdx, linearize)
        top_y_v = self.top_y.to_z3_var(confIdx, linearize)
        top_w_v = self.top_width.to_z3_var(confIdx, linearize)
        top_h_v = self.top_height.to_z3_var(confIdx, linearize)

        m = solver.model()
        def get(v):
            return float(m.get_interp(v).as_fraction())

        return Conformance(get(top_w_v), get(top_h_v), get(top_x_v), get(top_y_v))



    def synth(self, confs: List[Conformance], constraints: List[IConstraint]):

        solver = z3.Optimize()
        linearize = False

        namesMap = {}
        biases = self.buildBiases(constraints)
        axiomMap = {}

        for confIdx, conf in enumerate(confs):

            axiomMap = {**axiomMap, **self.addConfDims(solver, conf, confIdx, linearize=linearize)}
            # axiomMap = {**axiomMap, **self.addLayoutAxioms(solver, confIdx)}
            self.addLayoutAxioms(solver, confIdx)
            
        
        for constrIdx, constr in enumerate(constraints):
            cvname = "constr_var" + str(constrIdx)
            cvar = z3.Bool(cvname)

            namesMap[cvname] = constr
            solver.add_soft(cvar, biases[constr])

            for confIdx in range(len(confs)):
                solver.add(z3.Implies(cvar, constr.to_z3_expr(confIdx, linearize)))

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

        print("solving synth")
        chk = solver.check()
        if (str(chk) is 'sat'):

            constrValues = [v for v in solver.model().decls() if v.name() in namesMap]
            output = [namesMap[v.name()] for v in constrValues if solver.model().get_interp(v)]
            pruned = [c.shortStr() for c in constraints if c not in output]
            # print('output: ', [o.shortStr() for o in output])
            # print('pruned: ', pruned)

            vars = ['-undefined1', 'box37', 'box38']
            fields = ['center_y', 'bottom', 'top']
            # debugSolverValues(solver, vars, fields, 0)
            
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

    def genExtraConformances(self, lower: Conformance, upper: Conformance) -> List[Conformance]:
        # create 10 evenly spaced conformances on the range [min height/width...max height/width]
        extras = []
        scale = 10
        diff_h = (upper.height - lower.height)/(scale * 1.0)
        diff_w = (upper.width - lower.width)/(scale * 1.0)

        print('diffs: ', diff_h, diff_w)
        if diff_h == 0.0 and diff_w == 0.0:
            print('optimizing!')
            extras.append(self.max_conf)
            return extras
        
        # print('min/max:', self.max_conf, self.max_conf.width)
        for step in range(0,scale):
            new_c = Conformance(lower.width + diff_w * step, lower.height + diff_h * step, 0, 0)
            extras.append(new_c)

        return extras

    def verify(self, confs: AbstractSet[Conformance], constraints: List[IConstraint]):
        
        if len(constraints) < 1:
            return None
        
        solver = z3.Solver()
        linearize = False

        namesMap = {}
        confIdx = 0

        self.addLayoutAxioms(solver, confIdx)
        # self.addVerifDims(solver, linearize)

        axiomMap = {}

        for confIdx, conf in enumerate(confs):

            axiomMap = {**axiomMap, **self.addConfDims(solver, conf, confIdx, linearize=linearize)}
            self.addLayoutAxioms(solver, confIdx)

        for constr in constraints:
            solver.add(constr.to_z3_expr(confIdx, linearize))


        print("solving verify")
        chk = solver.check()
        if (str(chk) is 'sat'):
            return True
        elif (str(chk) is 'unsat'):
            # allConstraints = {**namesMap, **axiomMap}
            # incompat = [axiomMap[str(v)] for v in solver.unsat_core() if str(v) in axiomMap] + [namesMap[str(c)].shortStr() for c in solver.unsat_core() if str(c) in namesMap]
            # print('unsat!')
            # print('core: ', solver.unsat_core())
            # print('pretty: ', incompat)
            # print('values: ', [solver.model().get_interp(c.y) for c in incompat])
            return False
        else:
            print('unknown: ', chk)

    def __call__(self, initial_constraints: List[IConstraint]):

        curr_confs = [self.min_conf]
        all_confs = self.genExtraConformances(self.min_conf, self.max_conf)
        constraints = initial_constraints
        print('starting CEGIS')
        
        all_confs = all_confs[1:]
        for conf in all_confs:
            constraints = self.synth(curr_confs, constraints)
            
            satisfiable = self.verify(all_confs, constraints)

            if not satisfiable:
                # print('new conformance: ', new_conf)
                curr_confs.append(conf)
                iters += 1
            else:
                print('done in %d iters' % iters)
                # print('constraints: ', [c.shortStr() for c in constraints])
                return constraints
        return self.synth(curr_confs, constraints)

        


# assume: the layout of an element is independent from the layout of its children.

# let parent, (u, l) be the next parent, (upper, lower) bound.
#   * let cs be all constraints between immediate children of parent.
#   * pick a satisfiable subset of cs with uniform sampling in [u, l].
#     -- compile boxes to z3 and optimize
#   * for each child of parent:
#     ** let (u', l') be the result of linearly optimizing cs as required + 
#       child.width = 0 as optional, child.width = u as optional. 
#     ** add child, (u', l') 



class HierarchicalPruner(BlackBoxPruner):

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

        self.hierarchy = examples[0]
        self.examples = examples

        self.top_width = self.hierarchy.width_anchor
        self.top_height = self.hierarchy.height_anchor
        self.top_x = self.hierarchy.left_anchor
        self.top_y = self.hierarchy.top_anchor

        

    def genExtraConformances(self, lower: Conformance, upper: Conformance) -> List[Conformance]:
        # create 10 evenly spaced conformances on the range [min height/width...max height/width]
        extras = []
        scale = 10
        diff_h = (upper.height - lower.height)/(scale * 1.0)
        diff_w = (upper.width - lower.width)/(scale * 1.0)

        print('diffs: ', diff_h, diff_w)
        if diff_h == 0.0 and diff_w == 0.0:
            print('optimizing!')
            extras.append(self.max_conf)
            return extras
        
        # print('min/max:', self.max_conf, self.max_conf.width)
        for step in range(0,scale):
            new_c = Conformance(lower.width + diff_w * step, lower.height + diff_h * step, 0, 0)
            extras.append(new_c)

        return extras

    def relevantConstraint(self, focus: IView, c: IConstraint) -> bool:
        cvs = c.vars()

        if len(cvs) == 1:
            name = cvs.pop()
            for child in focus.children:
                if child.name == name:
                    return True
            return False
        else:
            if isinstance(c, PositionConstraint):
                return focus.is_parent_of_name(c.y.view_name) or (focus.is_parent_of_name(c.x.view_name) if c.x else False)
            if isinstance(c, SizeConstraint):
                return focus.is_parent_of_name(c.y.view_name) or (focus.is_parent_of_name(c.x.view_name) if c.x else False)

            

    # add axioms for width = right - left, width >= 0, height = bottom - top, height >= 0
    # specialized to a particular conformance

    # return a map from asserted layout axioms to explanatory strings
    def addLayoutAxioms(self, solver: z3.Optimize, focus: IView, confIdx: int, linearize: bool = False):

        output = {}

        for box in [focus, *focus.children]:
            w, h = box.width_anchor.to_z3_var(confIdx, linearize), box.height_anchor.to_z3_var(confIdx, linearize)
            l, r = box.left_anchor.to_z3_var(confIdx, linearize), box.right_anchor.to_z3_var(confIdx, linearize)
            t, b = box.top_anchor.to_z3_var(confIdx, linearize), box.bottom_anchor.to_z3_var(confIdx, linearize)
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

        
    def isWhole(self, c: IConstraint) -> bool:
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

    def addConfDims(self, solver: z3.Optimize, focus: IView, conf: Conformance, confIdx: int, linearize: bool = False):
        output = {}

        top_x_v = focus.left_anchor.to_z3_var(confIdx, linearize)
        top_y_v = focus.top_anchor.to_z3_var(confIdx, linearize)
        top_w_v = focus.width_anchor.to_z3_var(confIdx, linearize)
        top_h_v = focus.height_anchor.to_z3_var(confIdx, linearize)
        
        solver.assert_and_track(top_w_v == conf.width, "top_w_%d" % conf.width)
        solver.assert_and_track(top_h_v == conf.height, "top_h_%d" % conf.height)
        solver.assert_and_track(top_x_v == conf.x, "top_x_%d" % conf.x)
        solver.assert_and_track(top_y_v == conf.y, "top_y_%d" % conf.y)

        output["top_w_%d" % conf.width] = str(top_w_v) + " = " + str(conf.width)
        output["top_h_%d" % conf.height] = str(top_h_v) + " = " + str(conf.height)

        return output

    def inferChildConf(self, constrs: List[IConstraint], focus: IView, min_c: Conformance, max_c: Conformance) -> Tuple[Conformance, Conformance]:
        
        linear_solver = kiwisolver.Solver()
        for constr in constrs:
            linear_solver.addConstraint(constr.to_kiwi_constr())

        # get the min by suggesting 0, and the max by suggesting max_c

        widthvar = kiwisolver.Variable(str(focus.width_anchor))
        heightvar = kiwisolver.Variable(str(focus.height_anchor))
        xvar = kiwisolver.Variable(str(focus.left_anchor))
        yvar = kiwisolver.Variable(str(focus.top_anchor))

        linear_solver.addEditVariable(widthvar, 'strong')
        linear_solver.addEditVariable(heightvar, 'strong')
        linear_solver.addEditVariable(xvar, 'strong')
        linear_solver.addEditVariable(yvar, 'strong')

        linear_solver.suggestValue(widthvar, min_c.width)
        linear_solver.suggestValue(heightvar, min_c.height)
        linear_solver.suggestValue(xvar, min_c.x)
        linear_solver.suggestValue(yvar, min_c.y)

        linear_solver.updateVariables()

        focus_min = Conformance(widthvar.value(), heightvar.value(), xvar.value(), yvar.value())

        linear_solver.suggestValue(widthvar, max_c.width)
        linear_solver.suggestValue(heightvar, max_c.height)
        linear_solver.suggestValue(xvar, max_c.x)
        linear_solver.suggestValue(yvar, max_c.y)

        linear_solver.updateVariables()

        focus_max = Conformance(widthvar.value(), heightvar.value(), xvar.value(), yvar.value())
        
        return (focus_min, focus_max)

    def __call__(self, constraints: List[IConstraint]):

        biases = self.buildBiases(constraints)

        linearize = False
        
        
        axiomMap = {}

        worklist = []
        start = (self.hierarchy, self.examples, self.min_conf, self.max_conf)
        print('starting hierarchical pruning with ', start)
        worklist.append(start)
        outputConstrs = set()

        while len(worklist) > 0:
            focus, focus_examples, min_c, max_c = worklist.pop()

            useCegis = True

            relevant = [c for c in constraints if self.relevantConstraint(focus, c)]

            
            if useCegis:
                bounds = confs_to_bounds(min_c, max_c)
                ceg_solver = CegisPruner(focus_examples, bounds)
                output = ceg_solver(relevant)
                outputConstrs |= set(output)
            else:
                solver = z3.Optimize()
                confs = self.genExtraConformances(self.min_conf, self.max_conf)

                for confIdx, conf in enumerate(confs):

                    axiomMap = {**axiomMap, **self.addConfDims(solver, focus, conf, confIdx, linearize=linearize)}
                    axiomMap = {**axiomMap, **self.addLayoutAxioms(solver, focus, confIdx, linearize=linearize)}

                
                usedConstrs = set()
                namesMap = {}

                for constrIdx, constr in enumerate(relevant):
                    cvname = "constr_var" + str(constrIdx)
                    usedConstrs.add(cvname)
                    namesMap[cvname] = constr
                    cvar = z3.Bool(cvname)

                    solver.add_soft(cvar, biases[constr])

                    for confIdx in range(len(confs)):
                        solver.add(z3.Implies(cvar, constr.to_z3_expr(confIdx, linearize)))


                sanitys = []
                for constrIdx, constr in enumerate(relevant):
                    cvname = "constr_var" + str(constrIdx)
                    cvar = z3.Bool(cvname)

                    # captures = ['box0.center_x', 'box0.width']
                    captures = ['box0.height']
                    types = (AspectRatioSizeConstraint)

                    if str(constr.y) in captures and not isinstance(constr, types):
                        sanitys.append(constr)

                print("solving %s" % focus.name)
                # print("with conformances", min_c, max_c)
                # print('relevant constraints: ', [r.shortStr() for r in relevant])
                with open("debug-%s.smt2" % focus.name, 'w') as outfile:
                    print(solver.sexpr(), file=outfile)

                chk = solver.check()
                if (str(chk) is 'sat'):

                    constrValues = [v for v in solver.model().decls() if v.name() in usedConstrs]
                    output = [namesMap[v.name()] for v in constrValues if solver.model().get_interp(v)]
                    pruned = [c.shortStr() for c in relevant if c not in output]

                    
                    # debugSolverValues


                    # print('output: ', [o.shortStr() for o in output])
                    # print('pruned: ', pruned)

                    # print('diff: relevant - output ', set([r.shortStr() for r in relevant]) - set([o.shortStr() for o in output]))
                    # print('diff: relevant - (output + pruned) ', set([r.shortStr() for r in relevant]) - (set([o.shortStr() for o in output]) | set(pruned)))
                    # print('diff: (output + pruned) - relevant ', (set([o.shortStr() for o in output]) | set(pruned)) - set([r.shortStr() for r in relevant]))

                    outputConstrs |= set(output)
                elif (str(chk) is 'unsat'):
                    # allConstraints = {**namesMap, **axiomMap}
                    incompat = [axiomMap[str(v)] for v in solver.unsat_core() if str(v) in axiomMap] + [namesMap[str(c)].shortStr() for c in solver.unsat_core() if str(c) in namesMap]
                    print('unsat!')
                    print('core: ', solver.unsat_core())
                    print('pretty: ', incompat)
                    assert False
                    # print('values: ', [solver.model().get_interp(c.y) for c in incompat])
                else:
                    print('unknown: ', chk)
                    assert False

            # calculate child conformances, enqueue children

            for ci, child in enumerate(focus.children):
                clo, chi = self.inferChildConf(output, child, min_c, max_c)

                worklist.append((child, [fe.children[ci] for fe in focus_examples], clo, chi))

        return {c.fuzzify() for c in outputConstrs}


