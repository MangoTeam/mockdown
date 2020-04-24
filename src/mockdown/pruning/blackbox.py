from typing import Dict, List, AbstractSet, Set, Tuple, Optional, Collection

import kiwisolver  # type: ignore
import z3  # type: ignore

from .conformance import Conformance, confs_to_bounds, conformance_range, add_conf_dims
from .typing import IPruningMethod, ISizeBounds
from .util import anchor_equiv, short_str
from ..constraint import IConstraint, ConstraintKind
from ..integration import constraint_to_z3_expr, anchor_id_to_z3_var, constraint_to_kiwi
from ..model import IView
from ..typing import unreachable, NT

# from mockdown.model.bounds import SizeBounds, confs_to_bounds
# from mockdown.pruning.typing import PruningMethod
# from mockdown.model import IView
# from mockdown.model.conformance import Conformance
# from mockdown.model.constraint import *


def debugSolverValues(solver: z3.Optimize, variables: List[str], fields: List[str], idx: int) -> None:
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

class BlackBoxPruner(IPruningMethod):

    def __init__(self, examples: List[IView[NT]], bounds: ISizeBounds):

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

    

    # add axioms for width = right - left, width >= 0, height = bottom - top, height >= 0
    # specialized to a particular conformance

    # return a map from asserted layout axioms to explanatory strings
    def add_layout_axioms(self, solver: z3.Optimize, confIdx: int) -> None:

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
            solver.add(widthAx)
            solver.add(heightAx) 

            solver.add(w >= 0) 
            solver.add(h >= 0) 


    def add_conf_dims(self, solver: z3.Optimize, conf: Conformance, confIdx: int) -> None:

        return add_conf_dims(solver, conf, confIdx, (self.top_x, self.top_y, self.top_width, self.top_height))


    def __call__(self, constraints: List[IConstraint]) -> List[IConstraint]:

        # build up all of the constraint as Z3 objects

        # idents = set()
        solver = z3.Optimize()
        linearize = False

        namesMap = {}
        biases = self.build_biases(constraints)
        axiomMap: Dict[str, str] = {}

        confs = conformance_range(self.min_conf, self.max_conf)

        for confIdx, conf in enumerate(confs):
            self.add_conf_dims(solver, conf, confIdx)
            self.add_layout_axioms(solver, confIdx)

        for constrIdx, constr in enumerate(constraints):
            cvname = "constr_var" + str(constrIdx)
            cvar = z3.Bool(cvname)

            namesMap[cvname] = constr
            solver.add_soft(cvar, biases[constr])

            for confIdx in range(len(confs)):
                solver.add(z3.Implies(cvar, constraint_to_z3_expr(constr, confIdx)))

                # solver.assert_and_track(, cvar)

        # sanitys = []
        # for constrIdx, constr in enumerate(constraints):
        #     cvname = "constr_var" + str(constrIdx)
        #     cvar = z3.Bool(cvname)

        #     # captures = ['box0.center_x', 'box0.width']
        #     captures = ['box0.height']

        #     if str(constr.y_id) in captures and not constr.kind is ConstraintKind.SIZE_ASPECT_RATIO:
        #         sanitys.append(constr)
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
            # incompat = [axiomMap[str(v)] for v in solver.unsat_core() if str(v) in axiomMap] + [
            #     short_str(namesMap[str(c)]) for c in solver.unsat_core() if str(c) in namesMap]
            print('unsat!')
            print('core: ', solver.unsat_core())
            # print('pretty: ', incompat)
            # print('values: ', [solver.model().get_interp(c.y) for c in incompat])
        else:
            print('unknown: ', chk)

        # print("constraint:")
        # print(namesMap)

        return constraints

class CegisPruner(BlackBoxPruner):

    def __init__(self, examples: List[IView[NT]], bounds: ISizeBounds):

        super().__init__(examples, bounds)


    def add_verif_dims(self, solver: z3.Solver, linearize: bool = False) -> None:

        confIdx = 0

        top_x_v = anchor_id_to_z3_var(self.top_x.id, confIdx)
        top_y_v = anchor_id_to_z3_var(self.top_y.id, confIdx)
        top_w_v = anchor_id_to_z3_var(self.top_width.id, confIdx)
        top_h_v = anchor_id_to_z3_var(self.top_height.id, confIdx)
        
        solver.add(top_w_v >= self.min_conf.width)
        solver.add(top_h_v >= self.min_conf.height)
        solver.add(top_w_v <= self.max_conf.width)
        solver.add(top_h_v <= self.max_conf.height)

        solver.add(top_x_v >= self.min_conf.x)
        solver.add(top_y_v >= self.min_conf.y)
        solver.add(top_x_v <= self.max_conf.x)
        solver.add(top_y_v <= self.max_conf.y)

    def get_verif_dims(self, solver: z3.Solver) -> Conformance:

        confIdx = 0

        top_x_v = anchor_id_to_z3_var(self.top_x.id, confIdx)
        top_y_v = anchor_id_to_z3_var(self.top_y.id, confIdx)
        top_w_v = anchor_id_to_z3_var(self.top_width.id, confIdx)
        top_h_v = anchor_id_to_z3_var(self.top_height.id, confIdx)

        m = solver.model()
        def get(v: z3.Var) -> float:
            return float(m.get_interp(v).as_fraction())

        return Conformance(get(top_w_v), get(top_h_v), int(get(top_x_v)), int(get(top_y_v)))



    def synth(self, confs: List[Conformance], constraints: List[IConstraint]) -> List[IConstraint]:

        solver = z3.Optimize()

        namesMap = {}
        biases = self.build_biases(constraints)

        for confIdx, conf in enumerate(confs):

            self.add_conf_dims(solver, conf, confIdx)
            # axiomMap = {**axiomMap, **self.addLayoutAxioms(solver, confIdx)}
            self.add_layout_axioms(solver, confIdx)
            
        
        for constrIdx, constr in enumerate(constraints):
            cvname = "constr_var" + str(constrIdx)
            cvar = z3.Bool(cvname)

            namesMap[cvname] = constr
            solver.add_soft(cvar, biases[constr])

            for confIdx in range(len(confs)):
                solver.add(z3.Implies(cvar, constraint_to_z3_expr(constr, confIdx)))

                # solver.assert_and_track(, cvar)
                

        # sanitys = []
        # for constrIdx, constr in enumerate(constraints):
        #     cvname = "constr_var" + str(constrIdx)
        #     cvar = z3.Bool(cvname)

        #     # captures = ['box0.center_x', 'box0.width']
        #     captures = ['box0.height']
        #     types = (AspectRatioSizeConstraint)

        #     if str(constr.y) in captures and not isinstance(constr, types):
        #         sanitys.append(constr)

        print("solving synth")
        chk = solver.check()
        if (str(chk) is 'sat'):

            constrValues = [v for v in solver.model().decls() if v.name() in namesMap]
            output = [namesMap[v.name()] for v in constrValues if solver.model().get_interp(v)]
            pruned = [short_str(c) for c in constraints if c not in output]
            # print('output: ', [o.shortStr() for o in output])
            # print('pruned: ', pruned)

            vars = ['-undefined1', 'box37', 'box38']
            fields = ['center_y', 'bottom', 'top']
            # debugSolverValues(solver, vars, fields, 0)
            
            return output
        elif (str(chk) is 'unsat'):
            # allConstraints = {**namesMap, **axiomMap}
            # incompat = [axiomMap[str(v)] for v in solver.unsat_core() if str(v) in axiomMap] + [namesMap[str(c)].shortStr() for c in solver.unsat_core() if str(c) in namesMap]
            print('unsat!')
            print('core: ', solver.unsat_core())
            # print('pretty: ', incompat)
            # print('values: ', [solver.model().get_interp(c.y) for c in incompat])
        else:
            print('unknown: ', chk)

        # print("constraints:")
        # print(namesMap)

        return constraints

    def verify(self, confs: List[Conformance], constraints: List[IConstraint]) -> Optional[bool]:
        
        if len(constraints) < 1:
            return None
        
        solver = z3.Solver()
        confIdx = 0

        self.add_layout_axioms(solver, confIdx)

        for confIdx, conf in enumerate(confs):

            self.add_conf_dims(solver, conf, confIdx)
            self.add_layout_axioms(solver, confIdx)

        for constr in constraints:
            solver.add(constraint_to_z3_expr(constr, confIdx))


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
            return unreachable(chk)

    def __call__(self, initial_constraints: List[IConstraint]) -> List[IConstraint]:

        curr_confs = [self.min_conf]
        all_confs = conformance_range(self.min_conf, self.max_conf)
        constraints = initial_constraints
        print('starting CEGIS')
        iters = 0
        
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
#   * let cs be all constraint between immediate children of parent.
#   * pick a satisfiable subset of cs with uniform sampling in [u, l].
#     -- compile boxes to z3 and optimize
#   * for each child of parent:
#     ** let (u', l') be the result of linearly optimizing cs as required + 
#       child.width = 0 as optional, child.width = u as optional. 
#     ** add child, (u', l') 


class HierarchicalPruner(IPruningMethod):

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
        self.examples = examples

        self.top_width = self.hierarchy.width_anchor
        self.top_height = self.hierarchy.height_anchor
        self.top_x = self.hierarchy.left_anchor
        self.top_y = self.hierarchy.top_anchor

    def relevant_constraints(self, focus: IView[NT], c: IConstraint) -> bool:

        # Note: "I moved this here inline as it doesn't belong in Constraint."
        def variables(cn: IConstraint) -> Set[str]:
            return set({cn.y_id.view_name}) or set({cn.x_id.view_name} if cn.x_id is not None else {})

        cvs = variables(c)

        if len(cvs) == 1:
            name = cvs.pop()
            for child in focus.children:
                if child.name == name:
                    return True
            return False
        else:
            if c.kind in ConstraintKind.get_position_kinds():
                return focus.is_parent_of_name(c.y_id.view_name) or (
                    focus.is_parent_of_name(c.x_id.view_name) if c.x_id else False)
            elif c.kind in ConstraintKind.get_size_kinds():
                return focus.is_parent_of_name(c.y_id.view_name) or (
                    focus.is_parent_of_name(c.x_id.view_name) if c.x_id else False)
            else:
                assert False, 'weird constraint kind: ' + str(c.kind)
                return unreachable(c.kind)

    # add axioms for width = right - left, width >= 0, height = bottom - top, height >= 0
    # specialized to a particular conformance

    # return a map from asserted layout axioms to explanatory strings
    def add_layout_axioms(self, solver: z3.Optimize, confIdx: int, focus: IView[NT]) -> None:

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
            solver.add(widthAx)
            solver.add(heightAx)
            solver.add(w >= 0)
            solver.add(h >= 0)

    def infer_child_conf(self, constrs: List[IConstraint], focus: IView[NT], min_c: Conformance, max_c: Conformance) -> \
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

    def __call__(self, constraints: List[IConstraint]) -> List[IConstraint]:

        # idents = set()

        biases = self.build_biases(constraints)

        linearize = False

        axiomMap: Dict[str, str] = {}

        worklist = []
        start = (self.hierarchy, self.examples, self.min_conf, self.max_conf)
        print('starting hierarchical pruning with ', start)
        worklist.append(start)
        outputConstrs = set()

        while len(worklist) > 0:
            focus, focus_examples, min_c, max_c = worklist.pop()

            useCegis = True

            relevant = [c for c in constraints if self.relevant_constraints(focus, c)]

            
            if useCegis:
                bounds = confs_to_bounds(min_c, max_c)
                ceg_solver = CegisPruner(focus_examples, bounds)
                output = ceg_solver(relevant)
                outputConstrs |= set(output)
            else:
                solver = z3.Optimize()
                confs = conformance_range(self.min_conf, self.max_conf)

                for confIdx, conf in enumerate(confs):

                    add_conf_dims(solver, conf, confIdx, (focus.left_anchor, focus.top_anchor, focus.width_anchor, focus.height_anchor))
                    self.add_layout_axioms(solver, confIdx, focus)

                
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


                # sanitys = []
                # for constrIdx, constr in enumerate(relevant):
                #     cvname = "constr_var" + str(constrIdx)
                #     cvar = z3.Bool(cvname)

                #     # captures = ['box0.center_x', 'box0.width']
                #     captures = ['box0.height']
                #     types = (AspectRatioSizeConstraint)

                #     if str(constr.y) in captures and not isinstance(constr, types):
                #         sanitys.append(constr)

                print("solving %s" % focus.name)
                # print("with conformances", min_c, max_c)
                # print('relevant constraints: ', [r.shortStr() for r in relevant])
                with open("debug-%s.smt2" % focus.name, 'w') as outfile:
                    print(solver.sexpr(), file=outfile)

                chk = solver.check()
                if (str(chk) is 'sat'):

                    constrValues = [v for v in solver.model().decls() if v.name() in usedConstrs]
                    output = [namesMap[v.name()] for v in constrValues if solver.model().get_interp(v)]
                    # pruned = [c.shortStr() for c in relevant if c not in output]

                    
                    # debugSolverValues


                    # print('output: ', [o.shortStr() for o in output])
                    # print('pruned: ', pruned)

                    # print('diff: relevant - output ', set([r.shortStr() for r in relevant]) - set([o.shortStr() for o in output]))
                    # print('diff: relevant - (output + pruned) ', set([r.shortStr() for r in relevant]) - (set([o.shortStr() for o in output]) | set(pruned)))
                    # print('diff: (output + pruned) - relevant ', (set([o.shortStr() for o in output]) | set(pruned)) - set([r.shortStr() for r in relevant]))

                    outputConstrs |= set(output)
                elif (str(chk) is 'unsat'):
                    # allConstraints = {**namesMap, **axiomMap}
                    # incompat = [axiomMap[str(v)] for v in solver.unsat_core() if str(v) in axiomMap] + [namesMap[str(c)].shortStr() for c in solver.unsat_core() if str(c) in namesMap]
                    print('unsat!')
                    print('core: ', solver.unsat_core())
                    # print('pretty: ', incompat)
                    assert False
                    # print('values: ', [solver.model().get_interp(c.y) for c in incompat])
                else:
                    print('unknown: ', chk)
                    assert False

            # calculate child conformances, enqueue children

            for ci, child in enumerate(focus.children):
                clo, chi = self.infer_child_conf(output, child, min_c, max_c)

                worklist.append((child, [fe.children[ci] for fe in focus_examples], clo, chi))

        # return {c.fuzzify() for c in outputConstrs}
        return list(outputConstrs)


