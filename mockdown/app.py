import uvicorn
from starlette.applications import Starlette
from starlette.requests import Request
from starlette.responses import JSONResponse

from mockdown.logic import valid_constraints
from mockdown.model.constraint import IConstraint
from mockdown.model.view import ViewBuilder
from mockdown.visibility import visible_pairs

app = Starlette(debug=True)


@app.route('/')
async def synthesize(request: Request):
    examples_json = await request.json()

    # Promote single bare example to a singleton list.
    if isinstance(examples_json, dict):
        examples_json = list(examples_json)

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
