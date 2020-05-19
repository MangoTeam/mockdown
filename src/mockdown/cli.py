import json
import tempfile
import webbrowser
from fractions import Fraction
from typing import TextIO, Type

import click
import uvicorn  # type: ignore
from jinja2 import Environment, PackageLoader, select_autoescape

from mockdown.app import create_app
from mockdown.model import QViewLoader, RViewLoader, ZViewLoader


@click.group()
def cli() -> None:
    pass


@click.command()
@click.argument('input', type=click.File('r'))
@click.option('-nt',
              '--numeric-type',
              type=click.Choice(['R', 'Q', 'Z'], case_sensitive=False),
              default='R',
              help="Numeric type of input: real, rational, or integer.")
def run(input: TextIO, numeric_type: str) -> None:
    examples_json = json.load(input)
    if not isinstance(examples_json, list):
        examples_json = [examples_json]

    loader = {
        'R': RViewLoader,
        'Q': QViewLoader,
        'Z': ZViewLoader
    }[numeric_type]()  # todo: be able to actuallys supply non-default options

    examples = [loader.load_dict(ex_json) for ex_json in examples_json]
    print(examples)


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
