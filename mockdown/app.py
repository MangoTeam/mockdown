from fractions import Fraction
from typing import Dict, List, Union

from starlette.applications import Starlette
from starlette.middleware.cors import CORSMiddleware
from starlette.requests import Request
from starlette.responses import JSONResponse
from starlette.staticfiles import StaticFiles
from timing_asgi import TimingMiddleware, TimingClient
from timing_asgi.integrations import StarletteScopeToName

from .constraint import AbstractConstraint
from .heuristic.visibility import visible_pairs
from .logic import valid_constraints
from .model import ViewBuilder, IView
from .pruning import BlackBoxPruner, HierarchicalPruner, PruningMethodFactory, ISizeBounds

"""
This dictionary contains *factories* that produce pruning methods!
"""
PRUNING_METHODS: Dict[str, PruningMethodFactory] = {
    'none': lambda x, y: (lambda constraints: constraints),
    'baseline': BlackBoxPruner,
    'hierarchical': HierarchicalPruner,
}


async def synthesize(request: Request):
    request_json: dict = await request.json()
    examples_json: List[dict] = request_json['examples']

    bounds: ISizeBounds = request_json.get('bounds', {})

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
        constraint.train_view_many(examples)
        for constraint
        in all_constraints

    ]

    prune = PRUNING_METHODS[request_json.get('pruning', 'none')](examples, bounds)

    pruned_constraints = prune(trained_constraints)

    trained_constraints_json = [
        AbstractConstraint.to_dict(constraint)
        for constraint
        in pruned_constraints
        if not constraint.is_falsified
    ]

    return JSONResponse(trained_constraints_json)


def create_app(*, static_dir: str, static_path: str, **kwargs) -> Starlette:
    app = Starlette(debug=True)
    app.add_middleware(CORSMiddleware, allow_origins=['*'], allow_methods=['*'], allow_headers=['*'],
                       allow_credentials=True)

    app.add_route('/api/synthesize', synthesize, methods=['POST'])
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
