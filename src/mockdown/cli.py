import json
import tempfile
import webbrowser
from pprint import pprint
from typing import TextIO

import click
import sympy as sym  # type:ignore
import uvicorn  # type: ignore
from jinja2 import Environment, PackageLoader, select_autoescape

from mockdown.app import create_app
from mockdown.engine import DefaultMockdownEngine
from mockdown.instantiation import VisibilityConstraintInstantiator
from mockdown.learning.simple import SimpleConstraintLearning
from mockdown.model.view import ViewLoader


@click.group()
def cli() -> None:
    pass


@click.command()
@click.argument('input', type=click.File('r'))
@click.option('-nt',
              '--numeric-type',
              type=click.Choice(['N', 'R', 'Q', 'Z'], case_sensitive=False),
              default='N',
              help="Numeric type of input: number, real, rational, or integer.")
def run(input: TextIO, numeric_type: str) -> None:
    examples_json = json.load(input)["examples"]

    # Note: sym.Number _should_ generally "do the right thing"...
    number_factory = {
        'N': sym.Number,
        'R': sym.Float,
        'Q': sym.Rational,
        'Z': sym.Integer
    }[numeric_type]

    engine = DefaultMockdownEngine()
    loader = ViewLoader(number_factory=sym.Number)
    instantiator = VisibilityConstraintInstantiator()

    # 1. Load Examples

    examples = [loader.load_dict(ex_json) for ex_json in examples_json]
    pprint(examples)

    # 2. Instantiate Templates
    templates = instantiator.instantiate(examples)
    pprint(templates)

    # 3. Learn Constants.
    learning = SimpleConstraintLearning(samples=examples, templates=templates)
    constraints = [candidate.constraint
                   for candidates in learning.learn()
                   for candidate in candidates]

    print(json.dumps(
        [cn.to_dict() for cn in constraints],
        ensure_ascii=False,
        indent=2,
    ))


@click.command()
@click.argument('input_views', type=click.File('r'))
@click.argument('input_constraints', type=click.File('r'))
def display(input_views: TextIO, input_constraints: TextIO) -> None:
    tmp = tempfile.NamedTemporaryFile(mode='w', prefix='fnord-', suffix='.html', delete=False)

    loader = PackageLoader('mockdown.display', 'templates')
    env = Environment(
        loader=loader,
        autoescape=select_autoescape(['html', 'xml'])
    )

    # Kind of a hack. Using importlib.resources is probably more Pythonic but...
    kiwi_js_src = loader.get_source(env, 'js/flightlessbird.all.js')[0]

    template = env.get_template('default.html.jinja2')

    html = template.render(
        kiwi_js_src=kiwi_js_src
    )
    tmp.write(html)
    tmp.flush()
    tmp.close()

    webbrowser.open(f"file://{tmp.name}")


@click.command()
@click.option('--static-dir', default='static/', help="Path to static content directory.")
@click.option('--static-path', default='/', help="URL prefix to serve static content from.")
def serve(static_dir: str, static_path: str) -> None:
    click.echo("Starting mockdown...")
    app = create_app(static_dir=static_dir,
                     static_path=static_path)

    uvicorn.run(app, host='0.0.0.0', port=8000)


cli.add_command(run)
cli.add_command(serve)
cli.add_command(display)

if __name__ == '__main__':
    cli()
