import uvicorn
from starlette.applications import Starlette
from starlette.requests import Request
from starlette.responses import JSONResponse, HTMLResponse
from starlette.staticfiles import StaticFiles
from starlette.middleware.cors import CORSMiddleware

from mockdown.display.view import display_view
from mockdown.logic import valid_constraints
from mockdown.model.constraint import IConstraint
from mockdown.model.view import ViewBuilder
from mockdown.visibility import visible_pairs

import dominate.tags as html


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

    trained_constraints_json = [
        IConstraint.to_dict(constraint)
        for constraint
        in trained_constraints
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
                                scale=2,
                                extra_styles=("margin: 1rem;"
                                              "display: inline-block;"))
        container.add(view_div)

    return HTMLResponse(container.render())


def create_app(*, static_dir: str, static_path: str, **kwargs) -> Starlette:
    app = Starlette(debug=True)
    app.add_middleware(CORSMiddleware, allow_origins=['*'], allow_methods=['*'], allow_headers=['*'], allow_credentials=True)

    app.add_route('/api/synthesize', synthesize, methods=['POST'])
    app.add_route('/api/visualize', visualize, methods=['POST'])
    app.mount(static_path, app=StaticFiles(directory=static_dir), name='static')

    return app


default_app = create_app(static_dir='static/', static_path='/')
