from typing import Any, Dict, List

from starlette.applications import Starlette
from starlette.middleware.cors import CORSMiddleware
from starlette.requests import Request
from starlette.responses import JSONResponse
from starlette.staticfiles import StaticFiles
from timing_asgi import TimingClient, TimingMiddleware  # type: ignore
from timing_asgi.integrations import StarletteScopeToName  # type: ignore

from .engine import DefaultMockdownEngine
from .learning.simple import SimpleConstraintLearning
from .model import IView
from .model.view.loader import RViewLoader, QViewLoader
from .pruning import BlackBoxPruner, HierarchicalPruner, ISizeBounds, PruningMethodFactory, CegisPruner, bounds_from_json, MarginPruner, DynamicPruner


def avg_children(v: Any) -> float:
    return sum([len(box.children) for box in v if len(box.children) > 0])/len([x for x in v if len(x.children) > 0])


"""
This dictionary contains *factories* that produce pruning methods!
"""
PRUNING_METHODS: Dict[str, PruningMethodFactory] = {
    'none': MarginPruner,
    'baseline': BlackBoxPruner, 
    'cegis': CegisPruner,
    'hierarchical': HierarchicalPruner,
    'margins': MarginPruner,
    'dynamic': DynamicPruner
}

async def synthesize(request: Request) -> JSONResponse:
    request_json = await request.json()
    examples_json = request_json['examples']
    bounds = bounds_from_json(request_json.get('bounds', {}))
    unambig = request_json['unambig']

    engine = DefaultMockdownEngine()

    # RViewLoader just loads everything as floats.
    loader = RViewLoader()

    # Product a list of examples (IView's).
    examples: List[IView[float]] = [
        loader.load_dict(example_json)
        for example_json
        in examples_json
    ]

    templates = engine.instantiation_engine.instantiate(examples)

    learning = SimpleConstraintLearning(samples=examples, templates=templates)
    constraints = learning.learn()

    prune = PRUNING_METHODS[request_json.get('pruning', 'none')](examples, bounds, unambig)

    # amount_before = len(constraints)
    print('number of elements:', len([x for x in examples[0]]))
    print('avg children: ', avg_children(examples[0]))

    pruned_constraints = prune(constraints)[0]

    res = [
        constraint.to_dict()
        for constraint
        in pruned_constraints
    ]

    # print("picking reduced %d to %d" % (amount_before, len(res)))

    print('output constraints: ', len(pruned_constraints))

    return JSONResponse(res)


def create_app(*, static_dir: str, static_path: str, **_kwargs: Dict[str, Any]) -> Starlette:
    app = Starlette(debug=True)
    app.add_middleware(CORSMiddleware, allow_origins=['*'], allow_methods=['*'], allow_headers=['*'],
                       allow_credentials=True)

    app.add_route('/api/synthesize', synthesize, methods=['POST'])
    app.mount(static_path, app=StaticFiles(directory=static_dir), name='static')

    class StdoutTimingClient(TimingClient):
        def timing(self, metric_name, timing, tags=None) -> None:
            print(metric_name, timing, tags)

    app.add_middleware(
        TimingMiddleware,
        client=StdoutTimingClient(),
        metric_namer=StarletteScopeToName(prefix="mockdown", starlette_app=app)
    )

    return app


default_app = create_app(static_dir='static/', static_path='/')
