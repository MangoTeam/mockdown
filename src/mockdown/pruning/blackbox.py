import operator
from dataclasses import replace
from enum import Enum
from fractions import Fraction
from typing import Dict, List, Set, Tuple, Optional, Any, Generic, Sequence, Iterator, FrozenSet, cast, Iterable, \
    ItemsView

import sympy as sym
import z3  # type: ignore

from mockdown.constraint import IConstraint, ConstraintKind
from mockdown.constraint.constraint import ConstantConstraint
from mockdown.constraint.types import PRIORITY_STRONG
from mockdown.integration import constraint_to_z3_expr, anchor_id_to_z3_var, evaluate_constraints, \
    extract_model_valuations
from mockdown.learning import ConstraintCandidate
from mockdown.model import IView, IAnchor
from mockdown.model.primitives import h_attrs, v_attrs, Attribute
from mockdown.pruning.conformance import Conformance, confs_to_bounds, conformance_range, add_conf_dims, to_rect, \
    conf_zip
from mockdown.pruning.types import ISizeBounds, BasePruningMethod
from mockdown.pruning.util import short_str, to_frac
from mockdown.types import unreachable, NT


def is_x_constr(c: IConstraint) -> bool:

    hs_attrs = h_attrs | {Attribute.WIDTH}
    vs_attrs = v_attrs | {Attribute.HEIGHT}
    if c.x_id:
        if c.x_id.attribute in hs_attrs and c.y_id.attribute in hs_attrs:
            return True
        elif c.x_id.attribute in vs_attrs and c.y_id.attribute in vs_attrs:
            return False
        else:
            print(short_str(c))
            raise Exception('bad constraint with mixed dimensions')
    else:
        return c.y_id.attribute in hs_attrs


LogLevel = Enum('LogLevel', 'NONE ALL')

class BlackBoxPruner(BasePruningMethod, Generic[NT]):

    example: IView[NT]
    top_width: IAnchor[NT]
    top_height: IAnchor[NT]
    top_x: IAnchor[NT]
    top_y: IAnchor[NT]
    solve_unambig: bool
    log_level: LogLevel

    def __init__(self, examples: Sequence[IView[NT]], bounds: ISizeBounds, solve_unambig: bool, targets: Optional[Sequence[IView[NT]]] = None):

        bounds_frac = {k: to_frac(v) if v else None
                       for k, v in cast(ItemsView[str, Optional[Fraction]], bounds.items())}

        heights = [to_frac(v.height) for v in examples]
        widths = [to_frac(v.width) for v in examples]
        xs = [to_frac(v.left) for v in examples]
        ys = [to_frac(v.top) for v in examples]

        min_w = min(bounds_frac.get('min_w', None) or min(widths), min(widths))
        max_w = max(bounds_frac.get('max_w', None) or max(widths), max(widths))
        min_h = min(bounds_frac.get('min_h', None) or min(heights), min(heights))
        max_h = max(bounds_frac.get('max_h', None) or max(heights), max(heights))

        min_x = min(bounds_frac.get('min_x', None) or min(xs), min(xs))
        max_x = max(bounds_frac.get('max_x', None) or max(xs), max(xs))
        min_y = min(bounds_frac.get('min_y', None) or min(ys), min(ys))
        max_y = max(bounds_frac.get('max_y', None) or max(ys), max(ys))

        self.min_conf = Conformance(min_w, min_h, min_x, min_y)
        self.max_conf = Conformance(max_w, max_h, max_x, max_y)

        # print('min conf', self.min_conf)
        # print('max conf', self.max_conf)

        assert len(examples) > 0, "Pruner requires non-empty learning examples"

        # print('examples: ', [ex.name for ex in examples])
        self.example = examples[0]


        self.top_width = self.example.width_anchor
        self.top_height = self.example.height_anchor
        self.top_x = self.example.left_anchor
        self.top_y = self.example.top_anchor

        self.targets: Sequence[IView[NT]] = targets or [x for x in self.example]

        self.solve_unambig = solve_unambig
        self.log_level = LogLevel.NONE


    def add_determinism(self, solver: z3.Optimize, cmap: Dict[str, IConstraint], x_dim: bool) -> None:

        # print('candidate constraints: ') 
        # print([(c[0], short_str(c[1])) for c in cmap.items()])

        
        # deterministic: pick two of necessary dimensions for each box
            # sum(constraints_by_dimension) = 2

        # group constraints by their y_anchorid and include the z3 constraint name

        constrs_by_id : Dict[str, List[Tuple[str, IConstraint]]] = {str(a.id) : [] for box in self.targets for a in box.anchors if box.name != self.example.name}
        for z3_name, constr in cmap.items():
            if constr.y_id.view_name == self.example.name:
                continue
            key = str(constr.y_id)
            constrs_by_id[key].append((z3_name, constr))

        # print('constraints_by_id:')
        # print(constrs_by_id)

        # unique: pick at most one constraint for each dimension
            # sum(constraints_that_use_dim) = 1
        for yid, constrs in constrs_by_id.items():
            sum_prefix = "unique_var_" + yid
            summand = z3.IntVal(0)
            for idx, cnstrs in enumerate(constrs):
                z3_name = cnstrs[0]
                constr = cnstrs[1]
                item_var = z3.Int(sum_prefix + str(idx))
                solver.add(z3.Implies(z3.Bool(z3_name), item_var == 1))
                solver.add(z3.Implies(z3.Not(z3.Bool(z3_name)), item_var == 0))
                summand = summand + item_var
            solver.add(summand <= 1)
        # # deterministic: for each box, in each dimension, pick constraints for two of the four possible anchors
        for box in self.targets:
            if box.name == self.example.name:
                continue
            if x_dim:
                xdims = [box.left_anchor, box.right_anchor, box.width_anchor, box.center_x_anchor]
                sum_prefix = "determ_x_" + box.name
                summand = z3.IntVal(0)
                vidx = 0
                for var in xdims:
                    for cnstrs in constrs_by_id[str(var.id)]:
                        z3_name = cnstrs[0]
                        constr = cnstrs[1]
                        item_var = z3.Int(sum_prefix + str(vidx))
                        solver.add(z3.Implies(z3.Bool(z3_name), item_var == 1))
                        solver.add(z3.Implies(z3.Not(z3.Bool(z3_name)), item_var == 0))
                        summand = summand + item_var

                        vidx += 1
                solver.add(summand == 2)
            else:
                ydims = [box.top_anchor, box.bottom_anchor, box.height_anchor, box.center_y_anchor]
                sum_prefix = "determ_y_" + box.name
                summand = z3.IntVal(0)
                vidx = 0
                for var in ydims:
                    for cnstrs in constrs_by_id[str(var.id)]:
                        z3_name = cnstrs[0]
                        constr = cnstrs[1]
                        item_var = z3.Int(sum_prefix + str(vidx))
                        solver.add(z3.Implies(z3.Bool(z3_name), item_var == 1))
                        solver.add(z3.Implies(z3.Not(z3.Bool(z3_name)), item_var == 0))
                        summand = summand + item_var

                        vidx += 1
                solver.add(summand == 2)

        # self.add_linking(solver, cmap, constrs_by_id, x_dim=True)
        # self.add_linking(solver, cmap, constrs_by_id, x_dim=False)


    # TODO: this is horribly slow, and also it's unclear whether it's needed or not. For the moment don't use it.
    def add_linking(self, solver: z3.Solver, cmap: Dict[str, IConstraint], constrs_by_id: Dict[str, List[Tuple[str, IConstraint]]], x_dim: bool) -> None:
        # linking: in each set of child dims, at least two child dims must be externally determined

        def layers(box: IView[NT]) -> Iterator[Tuple[IView[NT], List[IView[NT]]]]:
            # for box in self.
            yield (box, list(box.children))
            # yield from chain(*map(layers, box.children))

        # print('layers:')
        # print(list(filter(lambda pcs: len(pcs[1]) > 0, layers(self.example))))

        def externally_determined(constr: IConstraint, parent: str) -> bool:
            if constr.kind == ConstraintKind.SIZE_CONSTANT:
                return True
            if constr.x_id:
                return constr.x_id.view_name == parent
            return True
        
        children = self.example.children
        parent = self.example
        suff = '_y'
        if x_dim:
            suff = '_x'

        anchors = z3.DeclareSort('Anchors' + suff)
        def make(a: IAnchor[NT]) -> Any:
            return z3.Const(str(a.id) + suff, anchors)

        
        root = z3.Const('root' + suff, anchors)

        link_one = z3.Function('link_one' + suff, anchors, anchors, z3.BoolSort())
        reach = z3.Function('reach' + suff, anchors, anchors, z3.BoolSort())

        v1, v2, v3 = z3.Consts('v1 v2 v3', anchors)
        reachable = z3.ForAll([v1, v2], z3.Implies(reach(v1, v2), \
            z3.Or(\
                z3.Exists([v3], z3.And(link_one(v1, v3), reach(v3, v2))),\
                link_one(v1,v2)
            )
        ))

        not_refl = z3.ForAll([v1], z3.Not(reach(v1, v1)))

        # TODO: these types are probably bogus
        def at_least_two(consts: List[z3.Const]) -> z3.ExprRef:
            output = z3.BoolVal(False)
            for l in consts:
                for r in consts:
                    if l == r:
                        continue
                output = z3.Or(output, z3.And(reach(root, l), reach(root, r)))
            return output

        if x_dim:
            parent_anchors = [parent.left_anchor, parent.right_anchor, parent.width_anchor, parent.center_x_anchor]
        else:
            parent_anchors = [parent.top_anchor, parent.bottom_anchor, parent.height_anchor, parent.center_y_anchor]
        for pa in parent_anchors:
            solver.add(link_one(root, make(pa)))
            solver.add(z3.Not(link_one(make(pa), root)))
            
        all_consts: List[z3.ExprRef] = [make(anc) for anc in parent_anchors] + [root]
        for box in children:
            if x_dim:
                child_anchors = [box.left_anchor, box.right_anchor, box.width_anchor, box.center_x_anchor]
            else:
                child_anchors = [box.top_anchor, box.bottom_anchor, box.height_anchor, box.center_y_anchor]

            for ci in range(len(child_anchors)):
                c_anc = make(child_anchors[ci])
                solver.add(z3.Not(link_one(root, c_anc)))
                for pi, p_anc in enumerate(parent_anchors):
                    solver.add(z3.Not(link_one(c_anc, make(p_anc))))
                    if pi != ci:
                        solver.add(z3.Not(link_one(make(p_anc), c_anc)))

            for ai, anc in enumerate(child_anchors):
                for fl_name, constr in constrs_by_id[str(anc.id)]:
                    if constr.x_id:
                        source = z3.Const(str(constr.x_id) + suff, anchors)
                    else:
                        source = make(parent_anchors[ai])

                    solver.add(z3.Implies(z3.Bool(fl_name), link_one(source, make(anc))))
                
                group_by_xid: Dict[str, List[Tuple[str, IConstraint]]] = {str(constr.x_id): [] for _, constr in cmap.items() if constr.x_id}
                for fl_name, constr in constrs_by_id[str(anc.id)]:
                        if constr.x_id:
                            key = str(constr.x_id)
                        else:
                            key = 'None'
                        if key in group_by_xid:
                            group_by_xid[key].append((fl_name, constr))
                        else:
                            group_by_xid[key] = [(fl_name, constr)]

                for source_name, constrs in group_by_xid.items():
                    if source_name == 'None':
                        continue
                    used_any = z3.BoolVal(False)
                    for fl_name, constr in constrs:
                        used_any = z3.Or(used_any, z3.Bool(fl_name))
                    solver.add(z3.Implies(z3.Not(used_any), z3.Not(link_one(z3.Const(source_name, anchors), make(anc)))))

            c_anc_consts = [make(anc) for anc in child_anchors]
            all_consts += c_anc_consts
            solver.add(at_least_two(c_anc_consts))
        
        for const in all_consts:
            solver.add(z3.Not(link_one(const, const)))

        # solver.add(at_least_two(c_consts))

        

        # solver.check()
        # print(solver.sexpr())
        bounded_bod = z3.BoolVal(False)
        for const in all_consts:
            bounded_bod = z3.Or(const == v1, bounded_bod)

        bounded = z3.ForAll([v1], bounded_bod)

        solver.add(not_refl)
        solver.add(reachable)
        solver.add(bounded)

        return

    # add axioms for top-level width = right - left, width >= 0, height = bottom - top, height >= 0
    # specialized to a particular conformance
    def add_conf_dims(self, solver: z3.Optimize, conf: Conformance, confIdx: int) -> None:

        return add_conf_dims(solver, conf, confIdx, (self.top_x, self.top_y, self.top_width, self.top_height))

    def synth_unambiguous(self, solver: z3.Optimize, names_map: Dict[str, IConstraint], confs: List[Conformance], x_dim: bool, dry_run: bool) -> Tuple[List[IConstraint], Dict[str, Fraction], Dict[str, Fraction]]:
    
        solver.push()
        invalid_candidates: Set[FrozenSet[str]] = set()
        iters = 0

        def get_ancs(v: IView[NT]) -> List[IAnchor[NT]]:
            if x_dim:
                return v.x_anchors
            else:
                return v.y_anchors

        while (True):
            for invalid_cand in invalid_candidates:
                control_term = z3.BoolVal(True)
                for control in invalid_cand:
                    control_term = z3.And(control_term, z3.Bool(control))
                solver.add(z3.Not(control_term))
            if self.log_level == LogLevel.ALL:
                with open("debug-%s-invalids-%d.smt2" % (self.example.name, iters), 'w') as debugout:
                    print(solver.sexpr(), file=debugout)

            


            if (solver.check() == z3.sat):
                constr_decls = [v for v in solver.model().decls() if v.name() in names_map]
                new_cand = frozenset([v.name() for v in constr_decls if solver.model().get_interp(v)])
                
                old_model = solver.model()

                solver.pop()
                solver.push()

                for control in new_cand:
                    solver.add(z3.Bool(control))

                # for conf_idx in range(len(confs)):
                conf_idx = len(confs)//2


                names = [str(a.id) for box in [self.example] + list(self.targets) for a in get_ancs(box)]
                
                vals = extract_model_valuations(old_model, conf_idx, names)
                for p_anc in get_ancs(self.example):
                    concrete_value = vals[str(p_anc.id)]
                    solver.add(anchor_id_to_z3_var(p_anc.id, conf_idx) == concrete_value)

                placement_term = z3.BoolVal(True)
                for child in self.targets:
                    if child.name == self.example.name:
                        continue
                    for c_anc in get_ancs(child):
                        concrete_value = vals[str(c_anc.id)]
                        placement_term = z3.And(placement_term, anchor_id_to_z3_var(c_anc.id, conf_idx) == concrete_value)
                solver.add(z3.Not(placement_term))

                if self.example.name == 'box13' and x_dim and self.log_level == LogLevel.ALL:
                    with open("debug-%s-determ-%d.smt2" % (self.example.name, iters), 'w') as debugout:
                        print(solver.sexpr(), file=debugout)

                if dry_run or solver.check() == z3.unsat:
                    if self.log_level != LogLevel.NONE: print('took %d iters' % iters)
                    constr_decls = [v for v in old_model.decls() if v.name() in names_map]
                    output = [names_map[v.name()] for v in constr_decls if old_model.get_interp(v)]

                    def get_ancs(v: IView[NT]) -> List[IAnchor[NT]]:
                        return v.x_anchors if x_dim else v.y_anchors
                    names = [str(a.id) for box in [self.example] + list(self.targets) for a in get_ancs(box)]

                    min_vals, max_vals = extract_model_valuations(old_model, 0, names), extract_model_valuations(old_model, len(confs)-1, names)
                    return (output, min_vals, max_vals)
                
                elif solver.check() == z3.sat:
                    # candidate is invalid
                    if new_cand in invalid_candidates:
                        raise Exception('inconceivable')
                    # print('new cand: ', new_cand)
                    invalid_candidates.add(new_cand)
                    solver.pop()
                    solver.push()
                    iters += 1
                    continue
                else:
                    # print('found it! with check value:', str(solver.check()))
                    print('unknown?', solver.check())
                    raise Exception('unexpected solver output')
                    
            else:
                raise Exception('cant find a solution')

    def reward_parent_relative(self, biases: Dict[IConstraint, float]) -> Dict[IConstraint, float]:
        for constr, score in biases.items():
            if constr.x_id:
                yv = self.example.find_anchor(constr.y_id)
                if yv and yv.view.is_parent_of_name(constr.x_id.view_name):
                    biases[constr] = score * 10
        return biases

    def __call__(self, cands: List[ConstraintCandidate]) -> Tuple[List[IConstraint], Dict[str, Fraction], Dict[str, Fraction]]:

        constraints = self.filter_constraints([c.constraint for c in cands])
        # print('after combining:')
        # print([short_str(c) for c in constraints])

        if self.log_level != LogLevel.NONE: print('candidates: ', len(constraints))


        if (len(constraints) == 0): 
            defaults: Dict[str, Fraction] = {}
            for box in self.example:
                for anchor in box.anchors:
                    defaults[str(anchor.id)] = to_frac(anchor.value)
            return (constraints, defaults, defaults)

        def add_box16w_hack(weights: Dict[IConstraint, float]) -> Dict[IConstraint, float]:
            for constr, weight in weights.items():
                if constr.y_id.view_name == 'box15' and constr.kind == ConstraintKind.SIZE_CONSTANT:
                    weights[constr] = 1000000
            return weights

        x_names: Dict[str, IConstraint] = {}
        y_names: Dict[str, IConstraint] = {}
        x_solver = z3.Optimize()
        y_solver = z3.Optimize()
        biases = self.build_biases(cands)
        if self.solve_unambig:
            biases = self.reward_parent_relative(biases)
        # biases = add_box16w_hack(biases)
        # biases = {k: 1 for k in biases}

        confs = conformance_range(self.min_conf, self.max_conf, scale=5)

        for constr_idx, constr in enumerate(constraints):
            cvname = "constr_var" + str(constr_idx)
            cvar = z3.Bool(cvname)

            if is_x_constr(constr):
                solver = x_solver
                names_map = x_names
            else:
                solver = y_solver
                names_map = y_names

            try:
                solver.add_soft(cvar, biases[constr])
            except Exception as e:
                print('missing constraint', short_str(constr))
                print('biases:')
                print(biases)
                raise e
            names_map[cvname] = constr
            

        for conf_idx, conf in enumerate(confs):
            self.add_conf_dims(x_solver, conf, conf_idx)
            self.add_conf_dims(y_solver, conf, conf_idx)
            self.add_layout_axioms(x_solver, conf_idx, self.targets, x_dim=True)
            self.add_layout_axioms(y_solver, conf_idx, self.targets, x_dim=False)

            for constr_idx, constr in enumerate(constraints):
                cvname = "constr_var" + str(constr_idx)
                cvar = z3.Bool(cvname)
                if is_x_constr(constr):
                    solver = x_solver
                else:
                    solver = y_solver
                solver.add(z3.Implies(cvar, constraint_to_z3_expr(constr, conf_idx)))

            

        # self.add_determinism(x_solver, x_names, x_dim=True)
        # self.add_determinism(y_solver, y_names, x_dim=False)

        if self.log_level == LogLevel.ALL:
            with open("debug-%s-initial-x.smt2" % self.example.name, 'w') as debugout:
                print(x_solver.sexpr(), file=debugout)
            with open("debug-%s-initial-y.smt2" % self.example.name, 'w') as debugout:
                print(y_solver.sexpr(), file=debugout)

        if self.solve_unambig:
            if self.log_level != LogLevel.NONE: print('solving for unambiguous horizontal layout')
            x_cs, x_min, x_max = self.synth_unambiguous(x_solver, x_names, confs, x_dim=True, dry_run=False)
            if self.log_level != LogLevel.NONE: print('solving for unambiguous vertical layout')
            y_cs, y_min, y_max = self.synth_unambiguous(y_solver, y_names, confs, x_dim=False, dry_run=False)
        else:
            if self.log_level != LogLevel.NONE: print('solving for horizontal layout')
            x_cs, x_min, x_max = self.synth_unambiguous(x_solver, x_names, confs, x_dim=True, dry_run=True)
            if self.log_level != LogLevel.NONE: print('solving for vertical layout')
            y_cs, y_min, y_max = self.synth_unambiguous(y_solver, y_names, confs, x_dim=False, dry_run=True)

        return (x_cs + y_cs, dict(x_min, **y_min), dict(x_max, **y_max))

# assume: the layout of an element is independent from the layout of its children.

# let parent, (u, l) be the next parent, (upper, lower) bound.
#   * let cs be all constraint between immediate children of parent.
#   * pick a satisfiable subset of cs with uniform sampling in [u, l].
#     -- compile boxes to z3 and optimize
#   * for each child of parent:
#     ** let (u', l') be the result of linearly optimizing cs as required + 
#       child.width = 0 as optional, child.width = u as optional. 
#     ** add child, (u', l') 


class HierarchicalPruner(BasePruningMethod):

    def __init__(self, examples: List[IView[NT]], bounds: ISizeBounds, solve_unambig: bool):

        bounds_frac = {k: to_frac(v) if v else None for k, v in bounds.items()}

        heights = [to_frac(v.height) for v in examples]
        widths = [to_frac(v.width) for v in examples]
        xs = [to_frac(v.left) for v in examples]
        ys = [to_frac(v.top) for v in examples]
        # print('min_w:')
        # print(min(widths))
        # print(type(min(widths)))
        # print(min(widths) + min(widths))
        # print(min(min(widths), min(widths)))

        min_w = min(bounds_frac.get('min_w', None) or min(widths), min(widths))
        max_w = max(bounds_frac.get('max_w', None) or max(widths), max(widths))
        min_h = min(bounds_frac.get('min_h', None) or min(heights), min(heights))
        max_h = max(bounds_frac.get('max_h', None) or max(heights), max(heights))

        min_x = min(bounds_frac.get('min_x', None) or min(xs), min(xs))
        max_x = max(bounds_frac.get('max_x', None) or max(xs), max(xs))
        min_y = min(bounds_frac.get('min_y', None) or min(ys), min(ys))
        max_y = max(bounds_frac.get('max_y', None) or max(ys), max(ys))

        self.min_conf = Conformance(min_w, min_h, min_x, min_y)
        self.max_conf = Conformance(max_w, max_h, max_x, max_y)

        assert len(examples) > 0, "Pruner requires non-empty learning examples"

        self.hierarchy = examples[0]
        self.examples = examples

        self.top_width = self.hierarchy.width_anchor
        self.top_height = self.hierarchy.height_anchor
        self.top_x = self.hierarchy.left_anchor
        self.top_y = self.hierarchy.top_anchor

        self.solve_unambig = solve_unambig
        self.log_level = LogLevel.NONE

    def relevant_constraint(self, focus: IView[NT], c: IConstraint) -> bool:

        if c.op != operator.eq: return False

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
            if c.kind.is_position_kind:
                return focus.is_parent_of_name(c.y_id.view_name) or (
                    focus.is_parent_of_name(c.x_id.view_name) if c.x_id else False)
            elif c.kind.is_size_kind:
                return focus.is_parent_of_name(c.y_id.view_name) or (
                    focus.is_parent_of_name(c.x_id.view_name) if c.x_id else False)
            else:
                assert False, 'weird constraint kind: ' + str(c.kind)
                return unreachable(c.kind)

    def infer_child_confs(self, constrs: List[IConstraint], focus: IView[NT], min_c: Conformance, max_c: Conformance) -> \
            Dict[str, Dict[str, Conformance]]:

        all_boxes = [focus] + [child for child in focus.children]

        x_solver = z3.Optimize()
        y_solver = z3.Optimize()

        z3_idx = 0 # just one z3 environment

        self.add_layout_axioms(x_solver, z3_idx, all_boxes, x_dim=True)
        self.add_layout_axioms(y_solver, z3_idx, all_boxes, x_dim=False)
        # self.add_containment_axioms(x_solver, z3_idx, focus, x_dim=True)
        # self.add_containment_axioms(y_solver, z3_idx, focus, x_dim=False)

        output: Dict[str, Dict[str, Conformance]] = {}

        # add parent dimensions
        p_w, p_h = anchor_id_to_z3_var(focus.width_anchor.id, z3_idx), anchor_id_to_z3_var(focus.height_anchor.id, z3_idx)
        p_x, p_y = anchor_id_to_z3_var(focus.left_anchor.id, z3_idx), anchor_id_to_z3_var(focus.top_anchor.id, z3_idx)

        x_solver.add(p_w <= max_c.width)
        y_solver.add(p_h <= max_c.height)
        x_solver.add(p_x <= max_c.x)
        y_solver.add(p_y <= max_c.y)

        x_solver.add(p_w >= min_c.width)
        y_solver.add(p_h >= min_c.height)
        x_solver.add(p_x >= min_c.x)
        y_solver.add(p_y >= min_c.y)

        for constr in constrs:
            if is_x_constr(constr):
                x_solver.add(constraint_to_z3_expr(constr, z3_idx))
            else:
                y_solver.add(constraint_to_z3_expr(constr, z3_idx))

        if self.log_level == LogLevel.ALL:
            with open("parent-dims-%s.smt2" % focus.name, 'w') as debugout:
                print(solver.sexpr(), file=debugout)
        
        for child in focus.children:
            c_w, c_h = anchor_id_to_z3_var(child.width_anchor.id, z3_idx), anchor_id_to_z3_var(child.height_anchor.id, z3_idx)
            c_x, c_y = anchor_id_to_z3_var(child.left_anchor.id, z3_idx), anchor_id_to_z3_var(child.top_anchor.id, z3_idx)

            max_vals: List[Fraction] = []
            min_vals: List[Fraction] = [] # TODO: this requires we iterate over values in the order that they're given to Conformance's constructor. fix this hack...
            # the order is width, height, x, y
            contexts = [(c_w, x_solver), (c_h, y_solver), (c_x, x_solver), (c_y, y_solver)]
            for var, solver in contexts:
                solver.push()
                solver.maximize(var)
                chk = solver.check()
                # with open("child-max-%s-%s.smt2" % (str(var), child.name), 'w') as debugout:
                #     print(solver.sexpr(), file=debugout)
                if chk == z3.sat:
                    val: Fraction = solver.model().get_interp(var).as_fraction()
                    max_vals.append(val)
                else:
                    print('check: ', str(chk))
                    with open("unsat-child-%s.smt2" % child.name, 'w') as debugout:
                        print(solver.sexpr(), file=debugout)
                    raise Exception('unsat child conformance %s in maximize' % child.name)
                
                solver.pop()
                solver.push()
                solver.minimize(var)
                # with open("child-min-%s-%s.smt2" % (str(var), child.name), 'w') as debugout:
                #     print(solver.sexpr(), file=debugout)
                chk = solver.check()
                if chk == z3.sat:
                    val = solver.model().get_interp(var).as_fraction()
                    min_vals.append(val)
                else:
                    print('check: ', str(chk))
                    with open("unsat-child-%s.smt2" % child.name, 'w') as debugout:
                        print(solver.sexpr(), file=debugout)
                    raise Exception('unsat child conformance %s in minimize' % child.name)
                solver.pop()
            

            output[child.name] = {'max': Conformance(*max_vals), 'min': Conformance(*min_vals)}

        return output

    def confs_to_constrs(self, child: IView[NT], min_c: Conformance, max_c: Conformance) -> Iterator[IConstraint]:
        
        kind = ConstraintKind.SIZE_CONSTANT
        for var, bound in conf_zip(min_c, child):
            yield ConstantConstraint(kind=kind, y_id=var.id, b=sym.Rational(bound), op=operator.ge)
        for var, bound in conf_zip(max_c, child):
            yield ConstantConstraint(kind=kind, y_id=var.id, b=sym.Rational(bound), op=operator.le)

    def integrate_constraints(self, examples: List[IView[NT]], min_c: Conformance, max_c: Conformance, constraints: List[IConstraint]) -> List[IConstraint]:
        result = BlackBoxPruner(examples, confs_to_bounds(min_c, max_c), self.solve_unambig)(constraints)[0]
        diff = set(constraints) - set(result)
        if len(diff) > 0:
            print('pruning during integration: ', [short_str(c) for c in diff])
            # raise Exception("foo")
        return result + [replace(constr, priority = PRIORITY_STRONG) for constr in diff]

    # sanity check: kiwi and z3 should both accept entire set of output constraints
    def validate_output_constrs(self, constraints: Set[ConstraintCandidate]) -> None:
        solver = z3.Optimize()
        bb_solver = BlackBoxPruner([self.hierarchy], confs_to_bounds(self.min_conf, self.max_conf), self.solve_unambig)
        baseline_set = set(bb_solver(list(constraints))[0])
        # print('output vs accepted:', len(output), len(constraints))
        
        inconceivables = constraints - baseline_set

        if (len(inconceivables) > 0):
            print('ERROR: black box found the following unsat core:')
            print([short_str(c.constraint) for c in inconceivables])

            evaluate_constraints(self.hierarchy, to_rect(self.min_conf), list(baseline_set))
            raise Exception('inconceivable')
        
        evaluate_constraints(self.hierarchy, to_rect(self.min_conf), list(constraints))

        return

    def __call__(self, cands: List[ConstraintCandidate]) -> Tuple[List[IConstraint], Dict[str, Fraction], Dict[str, Fraction]]:

        infer_with_z3 = True
        validate = False
        debug = True
        integrate = False

        # constraints = self.combine_bounds([c.constraint for c in cands])

        worklist = []
        start = (self.hierarchy, self.examples, self.min_conf, self.max_conf)
        if debug: print('starting hierarchical pruning with ', start)
        worklist.append(start)
        output_constrs = set()

        while len(worklist) > 0:
            focus, focus_examples, min_c, max_c = worklist.pop()
            if self.log_level != LogLevel.NONE: 
                print('solving for ', focus, 'with bounds ', min_c, max_c)

            relevant = [c for c in cands if self.relevant_constraint(focus, c.constraint)]

            targets = [focus] + [child for child in focus.children]

            bounds = confs_to_bounds(min_c, max_c)

            bb_solver = BlackBoxPruner(focus_examples, bounds, self.solve_unambig, targets=targets)
            bb_solver.log_level = self.log_level
            focus_output, mins, maxes = bb_solver(relevant)

            output_constrs |= set(focus_output)

            
            if integrate and len(focus_output) > 0: 
                int_output_constrs = set(self.integrate_constraints(self.examples, self.min_conf, self.max_conf, list(output_constrs)))
                output_constrs = int_output_constrs
            
            if validate: self.validate_output_constrs(output_constrs)

            if not infer_with_z3:
                child_confs = self.infer_child_confs(list(output_constrs), focus, min_c, max_c)

            for ci, child in enumerate(focus.children):

                def get(anc: IAnchor[NT]) -> str:
                    return str(anc.id)
                
                if infer_with_z3:
                    clo = Conformance(mins[get(child.width_anchor)], mins[get(child.height_anchor)], mins[get(child.left_anchor)], mins[get(child.top_anchor)])
                    chi = Conformance(maxes[get(child.width_anchor)], maxes[get(child.height_anchor)], maxes[get(child.left_anchor)], maxes[get(child.top_anchor)])
                else:
                    clo, chi = child_confs[child.name]['min'], child_confs[child.name]['max']

                worklist.append((child, [fe.children[ci] for fe in focus_examples], clo, chi))
            if self.log_level == LogLevel.ALL:
                with open('constraints.json', 'a') as debugout:
                    print([short_str(c) for c in focus_output], file=debugout)

        print('done with hierarchical pruning! finishing up...')
        if integrate: 
            output_constrs = set(self.integrate_constraints(self.examples, self.min_conf, self.max_conf, list(output_constrs)))

        if debug and validate: self.validate_output_constrs(output_constrs)

        if self.log_level != LogLevel.NONE: self.dump_constraints("output.smt2", self.hierarchy, list(output_constrs))

        return (list(output_constrs), {}, {})


