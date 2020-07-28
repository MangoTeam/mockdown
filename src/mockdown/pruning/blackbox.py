from typing import Dict, List, AbstractSet, Set, Tuple

import kiwisolver  # type: ignore
import z3  # type: ignore

from .conformance import Conformance
from .typing import IPruningMethod, ISizeBounds
from .util import anchor_equiv, short_str
from ..constraint import IConstraint, ConstraintKind
from ..integration import constraint_to_z3_expr, anchor_id_to_z3_var, constraint_to_kiwi
from ..model import IView
from ..typing import unreachable


class BlackBoxPruner(IPruningMethod):

    def __init__(self, examples: List[IView[float]], bounds: ISizeBounds):

        heights = [v.height for v in examples]
        widths = [v.width for v in examples]

        min_w = bounds.get('min_w', None) or int(min(widths))
        max_w = bounds.get('max_w', None) or int(max(widths))
        min_h = bounds.get('min_h', None) or int(min(heights))
        max_h = bounds.get('max_h', None) or int(max(heights))

        self.min_conf = Conformance(min_w, min_h, 0, 0)
        self.max_conf = Conformance(max_w, max_h, 0, 0)

        # print('min conf', self.min_conf)
        # print('max conf', self.max_conf)

        assert len(examples) > 0, "Pruner requires non-empty learning examples"

        self.example = examples[0]

        self.top_width = self.example.width_anchor
        self.top_height = self.example.height_anchor
        self.top_x = self.example.left_anchor
        self.top_y = self.example.top_anchor

    def genExtraConformances(self, **kwargs: Conformance) -> Set[Conformance]:
        # create 10 evenly spaced conformances on the range [min height/width...max height/width]
        extras = set()
        scale = 10
        diff_h = (self.max_conf.height - self.min_conf.height) / (scale * 1.0)
        diff_w = (self.max_conf.width - self.min_conf.width) / (scale * 1.0)

        if diff_h == 0 and diff_w == 0:
            # print('optimizing!')
            extras.add(self.max_conf)
            return extras

        # print('min/max:', self.max_conf, self.max_conf.width)
        for step in range(0, scale):
            new_c = Conformance(self.min_conf.width + diff_w * step,
                                self.min_conf.height + diff_h * step, 0, 0)
            extras.add(new_c)

        return extras

    # add axioms for width = right - left, width >= 0, height = bottom - top, height >= 0
    # specialized to a particular conformance

    # return a map from asserted layout axioms to explanatory strings
    def addLayoutAxioms(self, solver: z3.Optimize, confIdx: int, **kwargs: IView) -> Dict[str, str]:

        output = {}

        for box in self.example:
            w, h = anchor_id_to_z3_var(box.width_anchor.id, confIdx), \
                   anchor_id_to_z3_var(box.height_anchor.id, confIdx)
            l, r = anchor_id_to_z3_var(box.left_anchor.id, confIdx), \
                   anchor_id_to_z3_var(box.right_anchor.id, confIdx)
            t, b = anchor_id_to_z3_var(box.top_anchor.id, confIdx), \
                   anchor_id_to_z3_var(box.bottom_anchor.id, confIdx)
            widthAx = w == (r - l)
            heightAx = h == (b - t)

            # print('adding axioms:', widthAx, heightAx, w>=0, h >= 0)
            solver.assert_and_track(widthAx, "width_ax_%d" % confIdx)
            output["width_ax_%d" % confIdx] = "%s = (%s - %s)" % (
                box.width_anchor.name, box.left_anchor.name, box.right_anchor.name)
            solver.assert_and_track(heightAx, "height_ax_%d" % confIdx)
            output["height_ax_%d" % confIdx] = "%s = (%s - %s)" % (
                box.height_anchor.name, box.bottom_anchor.name, box.top_anchor.name)
            # , heightAx
            solver.assert_and_track(w >= 0, "pos_w_%d" % confIdx)
            solver.assert_and_track(h >= 0, "pos_w_%d" % confIdx)
            output["pos_w_%d" % confIdx] = "%s >= 0" % box.width_anchor.name
            output["pos_h_%d" % confIdx] = "%s >= 0" % box.height_anchor.name

        return output

    def checkSanity(self, constraints: List[IConstraint]) -> None:

        confs = self.genExtraConformances()

        print('checking constraint for sanity:', [short_str(x) for x in constraints])

        for confidx, conf in enumerate(confs):
            solver = z3.Optimize()
            self.addConfDims(solver, conf, confidx)
            self.addLayoutAxioms(solver, confidx)
            # solver.add
            for c in constraints:
                solver.add(constraint_to_z3_expr(c, confidx))

            m = solver.model()
            chk = solver.check()

            print('result for', conf)
            print(str(chk))

    def is_whole(self, c: IConstraint) -> bool:
        steps = [0.05 * x for x in range(20)]
        best_diff = float(min([abs(s - c.a) for s in steps]))
        return best_diff <= 0.01

    def make_pairs(self, constraints: List[IConstraint]) -> List[Tuple[IConstraint, IConstraint]]:
        return [(c, cp) for c in constraints for cp in constraints if anchor_equiv(c, cp) and c.op != cp.op]

    def build_biases(self, constraints: List[IConstraint]) -> Dict[IConstraint, float]:
        default = {c: 1.0 for c in constraints}

        pairs = self.make_pairs(constraints)
        # print([(x.shortStr(), y.shortStr()) for (x,y) in pairs][0])

        # reward specific constraint
        for c in constraints:
            score = 10
            # aspect ratios and size constraint are specific the more samples behind them
            if c.kind is ConstraintKind.SIZE_ASPECT_RATIO:
                # print(c, c.is_falsified)
                score = 1 if c.is_falsified else 100 * c.sample_count
            elif c.kind is ConstraintKind.SIZE_RATIO:
                # and doubly specific when the constants are nice
                if self.is_whole(c):
                    score = 1000 * c.sample_count
                else:
                    score = 100 * c.sample_count
            # positions are specific if they're paired and the pairs are close together
            elif c.kind in ConstraintKind.position_kinds:
                score = 1000
                # for simplicity we update pairs after this loop

            # if (isinstance(c, ))
            if c.is_falsified:
                score = 1  # discard!
            default[c] = score

        for (l, r) in pairs:
            if l.kind in ConstraintKind.position_kinds:
                assert r.kind in ConstraintKind.position_kinds

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
                    score = (-9990) / upper * diff + 10000
                    default[l] = score
                    default[r] = score

        return default

    def addConfDims(self, solver: z3.Optimize, conf: Conformance, confIdx: int, **kwargs: IView) -> Dict[str, str]:
        output = {}

        top_x_v = anchor_id_to_z3_var(self.top_x.id, confIdx)
        top_y_v = anchor_id_to_z3_var(self.top_y.id, confIdx)
        top_w_v = anchor_id_to_z3_var(self.top_width.id, confIdx)
        top_h_v = anchor_id_to_z3_var(self.top_height.id, confIdx)

        solver.assert_and_track(top_w_v == conf.width, "top_w_%d" % conf.width)
        solver.assert_and_track(top_h_v == conf.height, "top_h_%d" % conf.height)
        solver.assert_and_track(top_x_v == conf.x, "top_x_%d" % conf.x)
        solver.assert_and_track(top_y_v == conf.y, "top_y_%d" % conf.y)

        output["top_w_%d" % conf.width] = str(top_w_v) + " = " + str(conf.width)
        output["top_h_%d" % conf.height] = str(top_h_v) + " = " + str(conf.height)

        return output

    def __call__(self, constraints: List[IConstraint]) -> List[IConstraint]:

        # build up all of the constraint as Z3 objects

        # idents = set()
        solver = z3.Optimize()
        linearize = False

        namesMap = {}
        biases = self.build_biases(constraints)
        axiomMap: Dict[str, str] = {}

        confs = self.genExtraConformances()

        for confIdx, conf in enumerate(confs):
            axiomMap = {**axiomMap, **self.addConfDims(solver, conf, confIdx=linearize)}
            axiomMap = {**axiomMap, **self.addLayoutAxioms(solver, confIdx)}

        for constrIdx, constr in enumerate(constraints):
            cvname = "constr_var" + str(constrIdx)
            cvar = z3.Bool(cvname)

            namesMap[cvname] = constr
            solver.add_soft(cvar, biases[constr])

            for confIdx in range(len(confs)):
                solver.add(z3.Implies(cvar, constraint_to_z3_expr(constr, confIdx)))

                # solver.assert_and_track(, cvar)

        sanitys = []
        for constrIdx, constr in enumerate(constraints):
            cvname = "constr_var" + str(constrIdx)
            cvar = z3.Bool(cvname)

            # captures = ['box0.center_x', 'box0.width']
            captures = ['box0.height']

            if str(constr.y_id) in captures and not constr.kind is ConstraintKind.SIZE_ASPECT_RATIO:
                sanitys.append(constr)
        # self.checkSanity(sanitys)

        # print('z3 expr:')
        with open("debug.smt2", 'w') as debugout:
            print(solver.sexpr(), file=debugout)
            # assert False

        print("solving")
        chk = solver.check()
        if (str(chk) == 'sat'):

            constrValues = [v for v in solver.model().decls() if v.name() in namesMap]
            output = [namesMap[v.name()] for v in constrValues if solver.model().get_interp(v)]
            pruned = [short_str(c) for c in constraints if c not in output]
            print('output: ', [short_str(o) for o in output])
            print('pruned: ', pruned)

            return output
        elif (str(chk) == 'unsat'):
            # allConstraints = {**namesMap, **axiomMap}
            incompat = [axiomMap[str(v)] for v in solver.unsat_core() if str(v) in axiomMap] + [
                short_str(namesMap[str(c)]) for c in solver.unsat_core() if str(c) in namesMap]
            print('unsat!')
            print('core: ', solver.unsat_core())
            print('pretty: ', incompat)
            # print('values: ', [solver.model().get_interp(c.y) for c in incompat])
        else:
            print('unknown: ', chk)

        # print("constraint:")
        # print(namesMap)

        return constraints


# assume: the layout of an element is independent from the layout of its children.

# let parent, (u, l) be the next parent, (upper, lower) bound.
#   * let cs be all constraint between immediate children of parent.
#   * pick a satisfiable subset of cs with uniform sampling in [u, l].
#     -- compile boxes to z3 and optimize
#   * for each child of parent:
#     ** let (u', l') be the result of linearly optimizing cs as required + 
#       child.width = 0 as optional, child.width = u as optional. 
#     ** add child, (u', l') 


class HierarchicalPruner(BlackBoxPruner):

    def __init__(self, examples: List[IView[float]], bounds: ISizeBounds):

        heights = [v.height for v in examples]
        widths = [v.width for v in examples]

        min_w = bounds.get('min_w', None) or int(min(widths))
        max_w = bounds.get('max_w', None) or int(max(widths))
        min_h = bounds.get('min_h', None) or int(min(heights))
        max_h = bounds.get('max_h', None) or int(max(heights))

        self.min_conf = Conformance(min_w, min_h, 0, 0)
        self.max_conf = Conformance(max_w, max_h, 0, 0)

        # print('min conf', self.min_conf)
        # print('max conf', self.max_conf)

        assert len(examples) > 0, "Pruner requires non-empty learning examples"

        self.hierarchy = examples[0]

        self.top_width = self.hierarchy.width_anchor
        self.top_height = self.hierarchy.height_anchor
        self.top_x = self.hierarchy.left_anchor
        self.top_y = self.hierarchy.top_anchor

    def genExtraConformances(self, **kwargs: Conformance) -> Set[Conformance]:
        lower = kwargs.pop('lower')
        upper = kwargs.pop('upper')

        # create 10 evenly spaced conformances on the range [min height/width...max height/width]
        extras = set()
        scale = 10
        diff_h = (upper.height - lower.height) / (scale * 1.0)
        diff_w = (upper.width - lower.width) / (scale * 1.0)

        print('diffs: ', diff_h, diff_w)
        if diff_h == 0.0 and diff_w == 0.0:
            print('optimizing!')
            extras.add(self.max_conf)
            return extras

        # print('min/max:', self.max_conf, self.max_conf.width)
        for step in range(0, scale):
            new_c = Conformance(lower.width + diff_w * step, lower.height + diff_h * step, 0, 0)
            extras.add(new_c)

        return extras

    def relevantConstraint(self, focus: IView, c: IConstraint) -> bool:

        # Note: "I moved this here inline as it doesn't belong in Constraint."
        def variables(cn):
            return {cn.y_id.view_name} or ({cn.x_id.view_name} if cn.x_id is not None else {})

        cvs = variables(c)

        if len(cvs) == 1:
            name = cvs.pop()
            for child in focus.children:
                if child.name == name:
                    return True
            return False
        else:
            if c.kind in ConstraintKind.position_kinds:
                return focus.is_parent_of_name(c.y_id.view_name) or (
                    focus.is_parent_of_name(c.x_id.view_name) if c.x_id else False)
            elif c.kind in ConstraintKind.size_kinds:
                return focus.is_parent_of_name(c.y_id.view_name) or (
                    focus.is_parent_of_name(c.x_id.view_name) if c.x_id else False)
            else:
                raise Exception("should be unreachable!")

    # add axioms for width = right - left, width >= 0, height = bottom - top, height >= 0
    # specialized to a particular conformance

    # return a map from asserted layout axioms to explanatory strings
    def addLayoutAxioms(self, solver: z3.Optimize, confIdx: int, **kwargs: IView):
        focus = kwargs.pop('focus')
        output = {}

        for box in [focus, *focus.children]:
            w, h = anchor_id_to_z3_var(box.width_anchor.id, confIdx), \
                   anchor_id_to_z3_var(box.height_anchor.id, confIdx)
            l, r = anchor_id_to_z3_var(box.left_anchor.id, confIdx), \
                   anchor_id_to_z3_var(box.right_anchor.id, confIdx)
            t, b = anchor_id_to_z3_var(box.top_anchor.id, confIdx), \
                   anchor_id_to_z3_var(box.bottom_anchor.id, confIdx)
            widthAx = w == (r - l)
            heightAx = h == (b - t)

            # print('adding axioms:', widthAx, heightAx, w>=0, h >= 0)
            solver.assert_and_track(widthAx, "width_ax_%d" % confIdx)
            output["width_ax_%d" % confIdx] = "%s = (%s - %s)" % (
                box.width_anchor.name, box.left_anchor.name, box.right_anchor.name)
            solver.assert_and_track(heightAx, "height_ax_%d" % confIdx)
            output["height_ax_%d" % confIdx] = "%s = (%s - %s)" % (
                box.height_anchor.name, box.bottom_anchor.name, box.top_anchor.name)
            # , heightAx
            solver.assert_and_track(w >= 0, "pos_w_%d" % confIdx)
            solver.assert_and_track(h >= 0, "pos_w_%d" % confIdx)
            output["pos_w_%d" % confIdx] = "%s >= 0" % box.width_anchor.name
            output["pos_h_%d" % confIdx] = "%s >= 0" % box.height_anchor.name

        return output

    def is_whole(self, c: IConstraint) -> bool:
        steps = [0.05 * x for x in range(20)]
        bestDiff = min([abs(s - c.a) for s in steps])
        return bestDiff <= 0.01

    def make_pairs(self, constraints: List[IConstraint]):
        return [(c, cp) for c in constraints for cp in constraints if anchor_equiv(c, cp) and c.op != cp.op]

    def build_biases(self, constraints: List[IConstraint]):
        default = {c: 1 for c in constraints}

        pairs = self.make_pairs(constraints)
        # print([(x.shortStr(), y.shortStr()) for (x,y) in pairs][0])

        # reward specific constraint
        for c in constraints:
            score = 10
            # aspect ratios and size constraint are specific the more samples behind them
            if c.kind is ConstraintKind.SIZE_ASPECT_RATIO:
                # print(c, c.is_falsified)
                score = 1 if c.is_falsified else 100 * c.sample_count
            elif c.kind is ConstraintKind.SIZE_RATIO:
                # and doubly specific when the constants are nice
                if self.is_whole(c):
                    score = 1000 * c.sample_count
                else:
                    score = 100 * c.sample_count
            # positions are specific if they're paired and the pairs are close together
            elif c.kind in ConstraintKind.position_kinds:
                score = 1000
                # for simplicity we update pairs after this loop

            # if (isinstance(c, ))
            if c.is_falsified:
                score = 1  # discard!
            default[c] = score

        for (l, r) in pairs:
            if l.kind in ConstraintKind.position_kinds:
                assert r.kind in ConstraintKind.position_kinds

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
                    score = (-9990) / upper * diff + 10000
                    default[l] = score
                    default[r] = score

        return default

    def addConfDims(self, solver: z3.Optimize, conf: Conformance, confIdx: int, **kwargs: IView):
        focus = kwargs.pop('focus')
        output = {}

        top_x_v = anchor_id_to_z3_var(focus.left_anchor.id, confIdx)
        top_y_v = anchor_id_to_z3_var(focus.top_anchor.id, confIdx)
        top_w_v = anchor_id_to_z3_var(focus.width_anchor.id, confIdx)
        top_h_v = anchor_id_to_z3_var(focus.height_anchor.id, confIdx)

        solver.assert_and_track(top_w_v == conf.width, "top_w_%d" % conf.width)
        solver.assert_and_track(top_h_v == conf.height, "top_h_%d" % conf.height)
        solver.assert_and_track(top_x_v == conf.x, "top_x_%d" % conf.x)
        solver.assert_and_track(top_y_v == conf.y, "top_y_%d" % conf.y)

        output["top_w_%d" % conf.width] = str(top_w_v) + " = " + str(conf.width)
        output["top_h_%d" % conf.height] = str(top_h_v) + " = " + str(conf.height)

        return output

    def inferChildConf(self, constrs: List[IConstraint], focus: IView, min_c: Conformance, max_c: Conformance) -> \
            Tuple[Conformance, Conformance]:

        linear_solver = kiwisolver.Solver()
        for constr in constrs:
            linear_solver.addConstraint(constraint_to_kiwi(constr))

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

        # idents = set()

        biases = self.build_biases(constraints)

        linearize = False

        axiomMap: Dict[str, str] = {}

        worklist = []
        start = (self.hierarchy, self.min_conf, self.max_conf)
        print('starting hierarchical pruning with ', start)
        worklist.append(start)
        outputConstrs = set()

        while len(worklist) > 0:
            focus, min_c, max_c = worklist.pop()

            solver = z3.Optimize()
            confs = self.genExtraConformances(lower=self.min_conf, upper=self.max_conf)

            for confIdx, conf in enumerate(confs):
                axiomMap = {**axiomMap, **self.addConfDims(solver, conf, confIdx, focus=focus)}
                axiomMap = {**axiomMap, **self.addLayoutAxioms(solver, confIdx, focus=focus)}

            relevant = [c for c in constraints if self.relevantConstraint(focus, c)]
            usedConstrs = set()
            namesMap = {}

            for constrIdx, constr in enumerate(relevant):
                cvname = "constr_var" + str(constrIdx)
                usedConstrs.add(cvname)
                namesMap[cvname] = constr
                cvar = z3.Bool(cvname)

                solver.add_soft(cvar, biases[constr])

                for confIdx in range(len(confs)):
                    solver.add(z3.Implies(cvar, constraint_to_z3_expr(constr, confIdx)))

            sanitys = []
            for constrIdx, constr in enumerate(relevant):
                cvname = "constr_var" + str(constrIdx)
                cvar = z3.Bool(cvname)

                # captures = ['box0.center_x', 'box0.width']
                captures = ['box0.height']

                if str(constr.y_id) in captures and not constr.kind is ConstraintKind.SIZE_ASPECT_RATIO:
                    sanitys.append(constr)

            print("solving %s" % focus.name)
            print("with conformances", min_c, max_c)
            print('relevant constraint: ', [short_str(r) for r in relevant])
            with open("debug-%s.smt2" % focus.name, 'w') as outfile:
                print(solver.sexpr(), file=outfile)

            chk = solver.check()
            if (str(chk) == 'sat'):

                constrValues = [v for v in solver.model().decls() if v.name() in usedConstrs]
                output = [namesMap[v.name()] for v in constrValues if solver.model().get_interp(v)]
                pruned = [short_str(c) for c in relevant if c not in output]
                print('output: ', [short_str(o) for o in output])
                print('pruned: ', pruned)

                print('diff: relevant - output ',
                      set([short_str(r) for r in relevant]) - set([short_str(o) for o in output]))
                print('diff: relevant - (output + pruned) ',
                      set([short_str(r) for r in relevant]) - (set([short_str(o) for o in output]) | set(pruned)))
                print('diff: (output + pruned) - relevant ',
                      (set([short_str(o) for o in output]) | set(pruned)) - set([short_str(r) for r in relevant]))

                outputConstrs |= set(output)
            elif (str(chk) == 'unsat'):
                # allConstraints = {**namesMap, **axiomMap}
                incompat = [axiomMap[str(v)] for v in solver.unsat_core() if str(v) in axiomMap] + [
                    short_str(namesMap[str(c)]) for c in solver.unsat_core() if str(c) in namesMap]
                print('unsat!')
                print('core: ', solver.unsat_core())
                print('pretty: ', incompat)
                assert False
                # print('values: ', [solver.model().get_interp(c.y) for c in incompat])
            else:
                print('unknown: ', chk)
                assert False

            # calculate child conformances, enqueue children

            for child in focus.children:
                clo, chi = self.inferChildConf(output, child, min_c, max_c)

                worklist.append((child, clo, chi))

        return outputConstrs
