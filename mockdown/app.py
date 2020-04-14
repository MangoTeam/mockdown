from typing import Dict, List

from starlette.applications import Starlette
from starlette.middleware.cors import CORSMiddleware
from starlette.requests import Request
from starlette.responses import JSONResponse
from starlette.staticfiles import StaticFiles
from timing_asgi import TimingMiddleware, TimingClient  # type: ignore
from timing_asgi.integrations import StarletteScopeToName  # type: ignore

from .engine import OldMockdownEngine
from .model import ViewBuilder
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

    engine = OldMockdownEngine()

    # Product a list of examples (IView's).
    examples = [
        ViewBuilder.from_dict(example_json).to_view()
        for example_json
        in examples_json
    ]

    all_constraints = engine.instantiation_engine.instantiate(examples)

    # todo here

    trained_constraints = [
        constraint.train_view_many(examples)
        for constraint
        in all_constraints

    ]

    prune = PRUNING_METHODS[request_json.get('pruning', 'none')](examples, bounds)

    pruned_constraints = prune(trained_constraints)

    trained_constraints_json = [
        constraint.to_dict()
        for constraint
        in pruned_constraints
        # if not constraint.is_falsified
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
