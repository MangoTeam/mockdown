from typing import Dict, List, AbstractSet, Set, Tuple, Optional, Collection, Any, cast, Generic, Protocol, Sequence

from dataclasses import asdict

import kiwisolver  # type: ignore
import z3  # type: ignore
import json

from math import floor, ceil

from fractions import Fraction

from .conformance import Conformance, confs_to_bounds, conformance_range, add_conf_dims, from_rect, to_rect, conservative_round
from .typing import IPruningMethod, ISizeBounds
from .util import anchor_equiv, short_str
from ..constraint import IConstraint, ConstraintKind, check_against_view
from ..integration import constraint_to_z3_expr, anchor_id_to_z3_var, constraint_to_kiwi, add_linear_axioms, load_view_from_model, anchor_to_kv, kiwi_lookup, make_kiwi_env, evaluate_constraints, extract_model_valuations, add_linear_containment
from ..model import IView, IAnchor
from ..typing import unreachable, NT, to_int, NT_co, NT_contra, to_frac, round_down, round_up, round_frac

from mockdown.model.primitives import RRect

class BlackBoxPruner(IPruningMethod, Generic[NT]):

    example: IView[NT]
    top_width: IAnchor[NT]
    top_height: IAnchor[NT]
    top_x: IAnchor[NT]
    top_y: IAnchor[NT]

    def __init__(self, examples: Sequence[IView[NT]], bounds: ISizeBounds, targets: Optional[Sequence[IView[NT]]] = None):

        heights = [to_frac(v.height) for v in examples]
        widths = [to_frac(v.width) for v in examples]
        xs = [to_frac(v.left) for v in examples]
        ys = [to_frac(v.top) for v in examples]

        min_w = min(bounds.get('min_w', None) or min(widths), min(widths))
        max_w = max(bounds.get('max_w', None) or max(widths), max(widths))
        min_h = min(bounds.get('min_h', None) or min(heights), min(heights))
        max_h = max(bounds.get('max_h', None) or max(heights), max(heights))

        min_x = min(bounds.get('min_x', None) or min(xs), min(xs))
        max_x = max(bounds.get('max_x', None) or max(xs), max(xs))
        min_y = min(bounds.get('min_y', None) or min(ys), min(ys))
        max_y = max(bounds.get('max_y', None) or max(ys), max(ys))

        self.min_conf = Conformance(min_w, min_h, min_x, min_y)
        self.max_conf = Conformance(max_w, max_h, max_x, max_y)

        # print('min conf', self.min_conf)
        # print('max conf', self.max_conf)

        assert len(examples) > 0, "Pruner requires non-empty learning examples"

        self.example = examples[0] 

        self.top_width = self.example.width_anchor
        self.top_height = self.example.height_anchor
        self.top_x = self.example.left_anchor
        self.top_y = self.example.top_anchor

        self.targets: Sequence[IView[NT]] = targets or [x for x in self.example]

    

    # add axioms for top-level width = right - left, width >= 0, height = bottom - top, height >= 0
    # specialized to a particular conformance
    def add_conf_dims(self, solver: z3.Optimize, conf: Conformance, confIdx: int) -> None:

        return add_conf_dims(solver, conf, confIdx, (self.top_x, self.top_y, self.top_width, self.top_height))


    def __call__(self, constraints: List[IConstraint]) -> Tuple[List[IConstraint], Dict[str, Fraction], Dict[str, Fraction]]:

        if (len(constraints) == 0): 
            defaults: Dict[str, Fraction] = {}
            for box in self.example:
                for anchor in box.anchors:
                    defaults[str(anchor.id)] = to_frac(anchor.value)
            return (constraints, defaults, defaults)

        names_map: Dict[str, IConstraint] = {}
        solver = z3.Optimize()
        biases = self.build_biases(constraints)

        confs = conformance_range(self.min_conf, self.max_conf)

        for conf_idx, conf in enumerate(confs):
            self.add_conf_dims(solver, conf, conf_idx)
            self.add_layout_axioms(solver, conf_idx, self.targets)
            self.add_containment_axioms(solver, conf_idx, self.example)

        for constr_idx, constr in enumerate(constraints):
            cvname = "constr_var" + str(constr_idx)
            cvar = z3.Bool(cvname)

            names_map[cvname] = constr
            solver.add_soft(cvar, biases[constr])

            for conf_idx in range(len(confs)):
                solver.add(z3.Implies(cvar, constraint_to_z3_expr(constr, conf_idx)))

        with open("debug-%s.smt2" % self.example.name, 'w') as debugout:
            print(solver.sexpr(), file=debugout)

        # print("solving")
        chk = solver.check()
        if (str(chk) == 'sat'):

            constr_decls = [v for v in solver.model().decls() if v.name() in names_map]
            output = [names_map[v.name()] for v in constr_decls if solver.model().get_interp(v)]
            # pruned = [short_str(c) for c in constraints if c not in output]
            # print('output: ', [short_str(o) for o in output])
            # print('pruned: ', pruned)

            min_vals, max_vals = extract_model_valuations(solver.model(), 0, self.example.names), extract_model_valuations(solver.model(), conf_idx, self.example.names)

            return (output, min_vals, max_vals)
        elif (str(chk) == 'unsat'):
            print('unsat!')
            print('core: ', solver.unsat_core())
            print('constraints: ', constraints)
        else:
            print('unknown: ', chk)

        min_vals, max_vals = extract_model_valuations(solver.model(), 0, self.example.names), extract_model_valuations(solver.model(), conf_idx, self.example.names)

        return (constraints, min_vals, max_vals)

class CegisPruner(Generic[NT], BlackBoxPruner[NT]):

    def __init__(self, examples: Sequence[IView[NT]], bounds: ISizeBounds, targets: Optional[Sequence[IView[NT]]] = None):
        super().__init__(examples, bounds, targets)

    def add_counterex_bounds(self, solver: z3.Optimize) -> None:

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
        def get(v: z3.Var) -> Fraction:
            return cast(Fraction, m.get_interp(v).as_fraction())

        return Conformance(get(top_w_v), get(top_h_v), get(top_x_v), get(top_y_v))



    def synth(self, confs: List[Conformance], constraints: List[IConstraint]) -> List[IConstraint]:

        solver = z3.Optimize()

        namesMap = {}
        biases = self.build_biases(constraints)

        for conf_idx, conf in enumerate(confs):

            self.add_conf_dims(solver, conf, conf_idx)
            self.add_layout_axioms(solver, conf_idx, self.targets)
            
        
        for constrIdx, constr in enumerate(constraints):
            cvname = "constr_var" + str(constrIdx)
            cvar = z3.Bool(cvname)

            namesMap[cvname] = constr
            solver.add_soft(cvar, biases[constr])

            for conf_idx in range(len(confs)):
                solver.add(z3.Implies(cvar, constraint_to_z3_expr(constr, conf_idx)))

        with open("debug-synth.smt2", 'w') as debugout:
            print(solver.sexpr(), file=debugout)

        # print("solving synth")
        chk = solver.check()
        if (str(chk) is 'sat'):

            constrValues = [v for v in solver.model().decls() if v.name() in namesMap]
            output = [namesMap[v.name()] for v in constrValues if solver.model().get_interp(v)]
            # pruned = [short_str(c) for c in constraints if c not in output]

            # for conf_idx in range(len(confs)):

            #     solver_view = load_view_from_model(solver.model(), conf_idx, self.example)

            #     for constr in output:
            #         if not check_against_view(solver_view, constr):
            #             print('ERROR z3 model inconsistent with constraint: %s ' % str(constr))


            
            return output
        elif (str(chk) is 'unsat'):
            print('unsat!')
            print('core: ', solver.unsat_core())
        else:
            print('unknown: ', chk)

        return constraints

    def simple_verify(self, confs: List[Conformance], constraints: List[IConstraint]) -> Optional[bool]:
        
        if len(constraints) < 1:
            return None
        
        solver = z3.Optimize()

        for confIdx, conf in enumerate(confs):

            self.add_conf_dims(solver, conf, confIdx)
            self.add_layout_axioms(solver, confIdx, self.targets)

            for constr in constraints:
                solver.add(constraint_to_z3_expr(constr, confIdx))

        chk = solver.check()
        if (str(chk) == 'sat'):
            return True
        elif (str(chk) == 'unsat'):
            return False
        else:
            print('unknown: ', chk)
            return unreachable(chk)
    
    def counterex_verify(self, constraints: List[IConstraint]) -> Optional[Conformance]:
        
        if len(constraints) < 1:
            return None
        
        solver = z3.Optimize()

        conf_idx = 0


        self.add_counterex_bounds(solver)
        self.add_layout_axioms(solver, conf_idx, self.example)

        pred = z3.Not(constraint_to_z3_expr(constraints[0], conf_idx))

        for constr in constraints[1:]:
            pred = z3.Or(z3.Not(constraint_to_z3_expr(constr, conf_idx)), pred)

        solver.add(pred)

        with open("debug-verify-cx.smt2", 'w') as outfile:
            print(solver.sexpr(), file=outfile)


        # print("solving verify with confs", confs)
        chk = solver.check()
        
        if (str(chk) == 'sat'):
            cx = self.get_verif_dims(solver)
            return cx
        elif (str(chk) == 'unsat'):
            return None
        else:
            print('unknown: ', chk)
            return unreachable(chk)


    # NOTE: this complicated CEGIS doesn't seem to work and I'm not sure how to get it to work. Don't use it...
    def cegis_loop(self, initial_constraints: List[IConstraint]) -> List[IConstraint]:
        print('starting complex cegis')

        max_iters = 50
        curr_confs = [self.min_conf, self.max_conf]

        for iter in range(max_iters):
            candidate = self.synth(curr_confs, initial_constraints)

            possible_cx = self.counterex_verify(candidate)

            if possible_cx:
                print('counterexample: ', possible_cx)
                curr_confs += [possible_cx]
            else:
                print('done! iters:', iter)
                return candidate
        print('WARNING: finished cegis without passing verify, with confs:', curr_confs)
        return self.synth(curr_confs, initial_constraints)


    # Poor man's CEGIS algorithm: for a range of conformances, verify/synth against a sublist of the range
    def simple_cegis(self, initial_constraints: List[IConstraint]) -> List[IConstraint]:
        
        all_confs = conformance_range(self.min_conf, self.max_conf)

        constraints = initial_constraints
        # print('starting simple CEGIS for ', self.example.name)
        iters = 0
        
        first = all_confs[0]
        all_confs = all_confs[1:]
        curr_confs = [first]
        for conf in all_confs:
            constraints = self.synth(curr_confs, initial_constraints)
            
            finished = self.simple_verify([first] + all_confs, constraints)

            if not finished:
                # print('new conformance: ', new_conf)
                curr_confs.append(conf)
                iters += 1
            else:
                print('done in %d iters' % iters)
                
                return constraints

        
        print('WARNING: finished cegis without passing verify, for confs:', curr_confs)
        
        return self.synth(curr_confs, constraints)

    def __call__(self, initial_constraints: List[IConstraint]) -> Tuple[List[IConstraint], Dict[str, Fraction], Dict[str, Fraction]]:
        raise Exception("unimplemented")
        # return self.simple_cegis(initial_constraints)

        


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

        heights = [to_frac(v.height) for v in examples]
        widths = [to_frac(v.width) for v in examples]
        xs = [to_frac(v.left) for v in examples]
        ys = [to_frac(v.top) for v in examples]

        min_w = min(bounds.get('min_w', None) or min(widths), min(widths))
        max_w = max(bounds.get('max_w', None) or max(widths), max(widths))
        min_h = min(bounds.get('min_h', None) or min(heights), min(heights))
        max_h = max(bounds.get('max_h', None) or max(heights), max(heights))

        min_x = min(bounds.get('min_x', None) or min(xs), min(xs))
        max_x = max(bounds.get('max_x', None) or max(xs), max(xs))
        min_y = min(bounds.get('min_y', None) or min(ys), min(ys))
        max_y = max(bounds.get('max_y', None) or max(ys), max(ys))

        self.min_conf = Conformance(min_w, min_h, min_x, min_y)
        self.max_conf = Conformance(max_w, max_h, max_x, max_y)

        assert len(examples) > 0, "Pruner requires non-empty learning examples"

        self.hierarchy = examples[0]
        self.examples = examples

        self.top_width = self.hierarchy.width_anchor
        self.top_height = self.hierarchy.height_anchor
        self.top_x = self.hierarchy.left_anchor
        self.top_y = self.hierarchy.top_anchor

    def relevant_constraints(self, focus: IView[NT], c: IConstraint) -> bool:

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

    def infer_child_confs(self, constrs: List[IConstraint], focus: IView[NT], min_c: Conformance, max_c: Conformance) -> \
            Dict[str, Dict[str, Conformance]]:
        
        targets = [focus] + [c for c in focus.children]

        env = make_kiwi_env(targets)

        linear_solver = kiwisolver.Solver()
        
        add_linear_axioms(linear_solver, targets, env)
        add_linear_containment(linear_solver, env, focus)

        for constr in constrs:
            linear_solver.addConstraint(constraint_to_kiwi(constr, env) | 'strong')

        output: Dict[str, Dict[str, Tuple[NT, NT, NT, NT]]] = {c.name : {} for c in focus.children}

        widthvar = kiwi_lookup(focus.width_anchor, env)
        heightvar = kiwi_lookup(focus.height_anchor, env)
        xvar = kiwi_lookup(focus.left_anchor, env)
        yvar = kiwi_lookup(focus.top_anchor, env)

        linear_solver.addConstraint((widthvar == float(min_c.width)) | 'weak')
        linear_solver.addConstraint((heightvar == float(min_c.height)) | 'weak')
        linear_solver.addConstraint((xvar == float(min_c.x)) | 'weak')
        linear_solver.addConstraint((yvar == float(min_c.y)) | 'weak')

        linear_solver.updateVariables()
# 

        for child in focus.children:
            c_widthvar = kiwi_lookup(child.width_anchor, env)
            c_heightvar = kiwi_lookup(child.height_anchor, env)
            c_xvar = kiwi_lookup(child.left_anchor, env)
            c_yvar = kiwi_lookup(child.top_anchor, env)
            
            output[child.name]['min'] = ((c_widthvar.value()), (c_heightvar.value()), (c_xvar.value()), (c_yvar.value()))

        linear_solver.addConstraint((widthvar == float(max_c.width)) | 'medium')
        linear_solver.addConstraint((heightvar == float(max_c.height)) | 'medium')
        linear_solver.addConstraint((xvar == float(max_c.x)) | 'medium')
        linear_solver.addConstraint((yvar == float(max_c.y)) | 'medium')

        linear_solver.updateVariables()

        for child in focus.children:
            c_widthvar = kiwi_lookup(child.width_anchor, env)
            c_heightvar = kiwi_lookup(child.height_anchor, env)
            c_xvar = kiwi_lookup(child.left_anchor, env)
            c_yvar = kiwi_lookup(child.top_anchor, env)

            output[child.name]['max'] = ((c_widthvar.value()), (c_heightvar.value()), (c_xvar.value()), (c_yvar.value()))

        rounded_out: Dict[str, Dict[str, Conformance]] = {}

        for cn, cvs in output.items():
            rounded_out[cn] = {}
            lo, hi = conservative_round(cvs['min'], cvs['max'])
            rounded_out[cn]['min'] = lo
            rounded_out[cn]['max'] = hi

        return rounded_out

    # sanity check: kiwi and z3 should both accept entire set of output constraints
    def validate_output_constrs(self, constraints: Set[IConstraint]) -> None:
        solver = z3.Optimize()
        bb_solver = BlackBoxPruner([self.hierarchy], confs_to_bounds(self.min_conf, self.max_conf))
        baseline_set = set(bb_solver(list(constraints))[0])
        # print('output vs accepted:', len(output), len(constraints))
        
        inconceivables = constraints - baseline_set

        if (len(inconceivables) > 0):
            print('ERROR: black box found the following unsat core:')
            print([short_str(c) for c in inconceivables])

            evaluate_constraints(self.hierarchy, to_rect(self.min_conf), list(baseline_set))
            raise Exception('inconceivable')
        
        evaluate_constraints(self.hierarchy, to_rect(self.min_conf), list(constraints))

        return

    def __call__(self, constraints: List[IConstraint]) -> Tuple[List[IConstraint], Dict[str, Fraction], Dict[str, Fraction]]:

        use_cegis = False
        infer_with_z3 = True
        validate = False
        debug = True

        
        biases = self.build_biases(constraints)

        worklist = []
        start = (self.hierarchy, self.examples, self.min_conf, self.max_conf)
        if debug: print('starting hierarchical pruning with ', start)
        worklist.append(start)
        output_constrs = set()

        while len(worklist) > 0:
            focus, focus_examples, min_c, max_c = worklist.pop()
            if debug: print('solving for ', focus, 'with bounds ', min_c, max_c)

            relevant = [c for c in constraints if self.relevant_constraints(focus, c)]

            targets = [focus] + [child for child in focus.children]

            bounds = confs_to_bounds(min_c, max_c)

            if use_cegis:
                ceg_solver = CegisPruner(focus_examples, bounds, targets = targets)
                focus_output, mins, maxes = ceg_solver(relevant)
            else:
                bb_solver = BlackBoxPruner(focus_examples, bounds)
                focus_output, mins, maxes = bb_solver(relevant)

            if debug: print('adding: ', [short_str(c) for c in focus_output])
            output_constrs |= set(focus_output)
            
            if validate: self.validate_output_constrs(output_constrs)

            for ci, child in enumerate(focus.children):

                def get(anc: IAnchor[NT]) -> str:
                    return str(anc.id)
                
                if infer_with_z3:
                    clo = Conformance(mins[get(child.width_anchor)], mins[get(child.height_anchor)], mins[get(child.left_anchor)], mins[get(child.top_anchor)])
                    chi = Conformance(maxes[get(child.width_anchor)], maxes[get(child.height_anchor)], maxes[get(child.left_anchor)], maxes[get(child.top_anchor)])
                else:
                    child_confs = self.infer_child_confs(list(focus_output), focus, min_c, max_c)
                    clo, chi = child_confs[child.name]['min'], child_confs[child.name]['max']

                worklist.append((child, [fe.children[ci] for fe in focus_examples], clo, chi))

        
        self.validate_output_constrs(output_constrs)

        return (list(output_constrs), {}, {})


