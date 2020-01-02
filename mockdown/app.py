from typing import Iterable, Callable, Dict, List, AbstractSet

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
PruningMethodFactory = Callable[[List[IView]], PruningMethod]


class Conformance:
    @property
    def width(self) -> int:
        return self.__w
    @property
    def height(self) -> int:
        return self.__h

    # TODO: do we need x/y in top-level conformances? right now they're always 0
    @property
    def x(self) -> int:
        return self.__x
    @property
    def y(self) -> int:
        return self.__y

    def __str__(self):
        return "{x: %i, y: %i, h: %i, w: %i}" % (self.x, self.y, self.height, self.width)

    def __init__(self, x: int, y: int, h: int, w: int):
        self.__w = w
        self.__h = h
        self.__x = x
        self.__y = y

class BlackBoxPruner(PruningMethod):

    def __init__(self, examples: List[IView]):

        heights = [v.height for v in examples]
        widths = [v.width for v in examples]

        min_h, max_h = min(heights), max(heights)
        min_w, max_w = min(widths), max(widths)

        self.min_conf = Conformance(0,0, min_h, min_w)
        self.max_conf = Conformance(0,0, max_h, max_w)

        self.top_width = examples[0].width_anchor
        self.top_height = examples[0].height_anchor
        self.top_x = examples[0].left_anchor
        self.top_y = examples[0].top_anchor

        self.examples = set()

    def genExtraConformances(self) -> AbstractSet[Conformance]:
        # print('')
        # create 10 evenly spaced conformances on the range [min height/width...max height/width]
        extras = set()
        scale = 10
        diff_h = (self.max_conf.height - self.min_conf.height)/scale
        diff_w = (self.max_conf.width - self.min_conf.width)/scale
        for step in range(0,scale):
            new_c = Conformance(0, 0, self.min_conf.height + diff_h * step, self.min_conf.width + diff_w * step)
            # print('adding:', new_c)
            extras.add(new_c)
        # print('orig:')
        # print(self.min_conf)
        # print(self.max_conf)
        # print('extras:')
        # print(str(extras))
        return extras

    def __call__(self, constraints: List[IConstraint]):

        # build up all of the constraints as Z3 objects

        idents = set()
        solver = z3.Optimize()
        namesMap = {}

        confs = self.genExtraConformances()


        
        for constrIdx, constr in enumerate(constraints):
            cvname = "constr_var" + str(constrIdx)
            cvar = z3.Bool(cvname)

            namesMap[cvname] = constr
            solver.add_soft(cvar)

            for confIdx, conf in enumerate(confs):
                # print("adding:", z3.Implies(cvar, constr.to_z3_expr(confIdx)))
            
                solver.add(z3.Implies(cvar, constr.to_z3_expr(confIdx)))
                
                top_x_v = z3.Real(str(self.top_x) + "_" + str(confIdx))
                top_y_v = z3.Real(str(self.top_y) + "_" + str(confIdx))
                top_w_v = z3.Real(str(self.top_width) + "_" + str(confIdx))
                top_h_v = z3.Real(str(self.top_height) + "_" + str(confIdx))

                solver.add(top_x_v == conf.x, top_y_v == conf.y)
                solver.add(top_w_v == conf.width, top_h_v == conf.height)

        # solver.check()
        chk = solver.check()
        if (str(chk) is 'sat'):
            # print("result:")
            # print(solver.model())

            constrValues = [v for v in solver.model().decls() if v.name() in namesMap]
            output = [namesMap[v.name()] for v in constrValues if bool(v.as_ast())]
            # print(output)
            return output
        elif (str(chk) is 'unsat'):
            print('unsat!')
            # solver.unsat_core()
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
    'none': lambda _: (lambda constraints: constraints),
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

    prune = PRUNING_METHODS[request_json.get('pruning', 'baseline')](examples)

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
