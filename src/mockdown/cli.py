import json
import logging
import os
import tempfile
import webbrowser
from typing import TextIO, Literal, Optional

import click
import uvicorn  # type: ignore
from jinja2 import Environment, PackageLoader, select_autoescape

from mockdown.app import create_app
from mockdown.run import run_timeout as run_mockdown_timeout, MockdownResults
from mockdown.types import Tuple4

LOGLEVEL = os.environ.get('LOGLEVEL', 'WARN').upper()
logging.basicConfig(level=LOGLEVEL)


@click.group()
def cli() -> None:
    pass


@click.command()
@click.argument('input', type=click.File('r'))
@click.argument('output', type=click.File('w'))
@click.option('-nt',
              '--numeric-type',
              type=click.Choice(['N', 'R', 'Q', 'Z'], case_sensitive=False),
              default='N',
              show_default=True,
              help="Numeric type of input: number, real, rational, or integer.")
@click.option('-im',
              '--instantiation-method',
              type=click.Choice(['prolog', 'numpy'], case_sensitive=False),
              default='numpy',
              show_default=True,
              help="Instantiation method to use: prolog or numpy.")
@click.option('-lm',
              '--learning-method',
              type=click.Choice(['simple', 'noisetolerant'], case_sensitive=False),
              default='simple',
              show_default=True,
              help="Learning method to use: simple or noisetolerant.")
@click.option('-pm',
              '--pruning-method',
              type=click.Choice(['none', 'baseline', 'hierarchical'], case_sensitive=False),
              default='none',
              show_default=True,
              help="Pruning method to use: baseline or hierarchical.")
@click.option('-pb',
              '--pruning-bounds',
              nargs=4,
              type=str,
              default=['-', '-', '-', '-'],
              show_default=True,
              metavar="MIN_W MIN_H MAX_W MAX_H",
              help="Bounds within which to do pruning. Use - for unspecified.")
@click.option('-dn',
              '--debug-noise',
              type=float,
              default=0,
              show_default=True,
              metavar="STDEV",
              help="Scale of (Gaussian) noise to apply to input. (For testing/debugging purposes)")
@click.option('-di',
              '--debug-instantiation',
              is_flag=True,
              type=bool,
              default=False,
              help="If true, instantiated templates are returned, and no learning or pruning is performed.")
@click.option('-to',
              '--timeout',
              type=int,
              default=None,
              show_default=True,
              help="Timeout after which synthesis will be aborted.")
def run(input: TextIO,
        output: TextIO,
        numeric_type: Literal["N", "Z", "Q", "R"],
        instantiation_method: Literal['prolog', 'numpy'],
        learning_method: Literal['prolog', 'noisetolerant'],
        pruning_method: Literal['none', 'baseline', 'hierarchical'],
        pruning_bounds: Tuple4[str],
        debug_noise: float,
        debug_instantiation: bool,
        timeout: Optional[int]) -> None:
    # Note, this return value is intercepted by `process_result` above!
    input_data = json.load(input)
    input.close()
    results = run_mockdown_timeout(input_data, options=dict(
        numeric_type=numeric_type,
        instantiation_method=instantiation_method,
        learning_method=learning_method,
        pruning_method=pruning_method,
        pruning_bounds=tuple((int(s) if s.isnumeric() else None for s in pruning_bounds)),
        debug_noise=debug_noise,
        debug_instantiation=debug_instantiation
    ), timeout=timeout)

    click.echo(json.dumps(
        results,
        ensure_ascii=False,
        indent=2,
    ), file=output)


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
    app = create_app(static_dir=static_dir,
                     static_path=static_path)

    uvicorn.run(app, host='0.0.0.0', port=8000)


cli.add_command(run)
cli.add_command(serve)
cli.add_command(display)

if __name__ == '__main__':
    cli()
