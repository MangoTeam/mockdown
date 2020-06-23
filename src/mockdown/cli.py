import json
import tempfile
import webbrowser
from typing import TextIO

import click
import uvicorn  # type: ignore
from jinja2 import Environment, PackageLoader, select_autoescape

from mockdown.app import create_app
from mockdown.run import run as run_mockdown


@click.group()
def cli() -> None:
    pass


@cli.resultcallback()
def process_result(result: dict) -> None:
    click.echo(json.dumps(
        result,
        ensure_ascii=False,
        indent=2,
    ))


@click.command()
@click.argument('input_io', type=click.File('r'))
@click.option('-nt',
              '--numeric-type',
              type=click.Choice(['N', 'R', 'Q', 'Z'], case_sensitive=False),
              default='N',
              help="Numeric type of input: number, real, rational, or integer.")
@click.option('-pm',
              '--pruning-method',
              type=click.Choice(['none', 'baseline', 'hierarchical'], case_sensitive=False),
              default='none',
              help="Pruning method to use: baseline or hierarchical.")
def run(input_io: TextIO, numeric_type: str, pruning_method: str) -> dict:
    # Note, this return value is intercepted by `process_result` above!
    return run_mockdown(input_io, numeric_type, pruning_method)


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
