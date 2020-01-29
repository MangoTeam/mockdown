from typing import Iterable, Callable, Dict, List, AbstractSet, Tuple
from dataclasses import dataclass

import uvicorn
from starlette.applications import Starlette
from starlette.requests import Request
from starlette.responses import JSONResponse, HTMLResponse
from starlette.staticfiles import StaticFiles
from starlette.middleware.cors import CORSMiddleware

from timing_asgi import TimingMiddleware, TimingClient
from timing_asgi.integrations import StarletteScopeToName

from mockdown.display.view import display_view
from mockdown.logic import valid_constraints
from mockdown.model import IView
from mockdown.model.constraint import IConstraint
from mockdown.model.view import ViewBuilder
from mockdown.visibility import visible_pairs

import z3

import dominate.tags as html

PruningMethod = Callable[[List[IConstraint]], List[IConstraint]]
PruningMethodFactory = Callable[[List[IView], Tuple[int, int]], PruningMethod]

@dataclass(frozen=True)
class Conformance:
    width: int
    height: int

    # TODO: do we need x/y in top-level conformances? right now they're always 0
    x: int
    y: int



class BlackBoxPruner(PruningMethod):

    def __init__(self, examples: List[IView], dimensions: (int, int)):

        heights = [v.height for v in examples]
        widths = [v.width for v in examples]

        min_h, max_h = min(heights), max(heights)
        # min_w, max_w = min(widths), max(widths)
        min_w, max_w = dimensions

        self.min_conf = Conformance(min_w, min_h, 0,0)
        self.max_conf = Conformance(max_w, max_h, 0,0)

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


class FancyPruning(PruningMethod):
    def __init__(self, examples: List[IView]):
        pass

    def __call__(self, constraints: List[IConstraint]):
        return constraints


"""
This dictionary contains *factories* that produce pruning methods!
"""
PRUNING_METHODS: Dict[str, PruningMethodFactory] = {
    'none': lambda x, y: (lambda constraints: constraints),
    'baseline': BlackBoxPruner,  # put it here
    'fancy': FancyPruning
}


async def synthesize(request: Request):
    request_json = await request.json()
    examples_json = request_json['examples']
   

    # Product a list of examples (IView's).
    examples = [
        ViewBuilder.from_dict(example_json).to_view()
        for example_json
        in examples_json
    ]

    edge_pair_sets = [
        visible_pairs(example, deep=True)
        for example
        in examples
    ]

    anchor_pair_sets = [
        [(e1.anchor, e2.anchor) for (e1, e2) in edge_pair_set]
        for edge_pair_set
        in edge_pair_sets
    ]

    constraint_sets = [
        list(valid_constraints(examples[i], anchor_pair_sets[i]))
        for i
        in range(len(examples))
    ]

    all_constraints = list(set().union(*constraint_sets))

    trained_constraints = [
        constraint.train_view_many(*examples)
        for constraint
        in all_constraints
    ]

    lo, hi = request_json['lower'], request_json['upper']

    prune = PRUNING_METHODS[request_json.get('pruning', 'none')](examples, (lo, hi))
    

    pruned_constraints = prune(trained_constraints)

    trained_constraints_json = [
        IConstraint.to_dict(constraint)
        for constraint
        in pruned_constraints
        if not constraint.is_falsified
    ]

    return JSONResponse(trained_constraints_json)


async def visualize(request: Request):
    request_json = await request.json()
    examples_json = request_json['examples']
    constraints_json = request_json['constraints']

    # Product a list of examples (IView's).
    examples = [
        ViewBuilder.from_dict(example_json).to_view()
        for example_json
        in examples_json
    ]

    constraints = [
        IConstraint.from_dict(constraint_json)
        for constraint_json
        in constraints_json
    ]

    container = html.div()
    for i in range(len(examples)):
        view_div = display_view(examples[i],
                                constraints=constraints,
                                scale=3,
                                extra_styles=("margin: 1rem;"
                                              "display: inline-block;"))
        container.add(view_div)

    return HTMLResponse(container.render())


def create_app(*, static_dir: str, static_path: str, **kwargs) -> Starlette:
    app = Starlette(debug=True)
    app.add_middleware(CORSMiddleware, allow_origins=['*'], allow_methods=['*'], allow_headers=['*'],
                       allow_credentials=True)

    app.add_route('/api/synthesize', synthesize, methods=['POST'])
    app.add_route('/api/visualize', visualize, methods=['POST'])
    app.mount(static_path, app=StaticFiles(directory=static_dir), name='static')

    class StdoutTimingClient(TimingClient):
        def timing(self, metric_name, timing, tags=None):
            print(metric_name, timing, tags)

    app.add_middleware(
        TimingMiddleware,
        client=StdoutTimingClient(),
        metric_namer=StarletteScopeToName(prefix="mockdown", starlette_app=app)
    )

    return app


default_app = create_app(static_dir='static/', static_path='/')
