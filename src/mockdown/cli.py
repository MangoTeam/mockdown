import json
import logging
import os
import tempfile
import webbrowser
from typing import TextIO, Literal, Optional, Tuple

import click
import uvicorn  # type: ignore
from jinja2 import Environment, PackageLoader, select_autoescape

from mockdown.app import create_app
from mockdown.run import run_timeout as run_mockdown_timeout, MockdownResults
from mockdown.scraping import Scraper
from mockdown.types import Tuple4

LOGLEVEL = os.environ.get('LOGLEVEL', 'WARN').upper()
logging.basicConfig(level=LOGLEVEL)


@click.group()
def cli() -> None:
    pass


@click.command()
@click.argument('input', type=click.File('r'))
@click.argument('output', type=click.File('w'))
@click.option('-if',
              '--input-format',
              type=click.Choice(['default', 'bench'], case_sensitive=False),
              default='default',
              show_default=True,
              help="Input format: either default, or bench_cache/*.json format")
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
              type=click.Choice(['simple', 'heuristic', 'noisetolerant'], case_sensitive=False),
              default='noisetolerant',
              show_default=True,
              help="Learning method to use: simple or noisetolerant.")
@click.option('-pm',
              '--pruning-method',
              type=click.Choice(['none', 'baseline', 'hierarchical'], case_sensitive=False),
              default='hierarchical',
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
@click.option('-dv',
              '--debug-visibilities',
              is_flag=True,
              type=bool,
              default=False,
              help="If true, detected visibilities are returned, and no instantiation, learning or pruning is performed.")
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
@click.option('-n',
              '--num-examples',
              type=int,
              default=None,
              show_default=True,
              help="Number of examples to use.")
def run(input: TextIO,
        output: TextIO,
        input_format: Literal['default', 'bench'],
        numeric_type: Literal["N", "Z", "Q", "R"],
        instantiation_method: Literal['prolog', 'numpy'],
        learning_method: Literal['prolog', 'noisetolerant'],
        pruning_method: Literal['none', 'baseline', 'hierarchical'],
        pruning_bounds: Tuple4[str],
        debug_noise: float,
        debug_visibilities: bool,
        debug_instantiation: bool,
        timeout: Optional[int],
        num_examples: Optional[int]) -> None:
    # Note, this return value is intercepted by `process_result` above!
    input_data = json.load(input)
    input.close()

    bounds = [None, None, None, None]
    for i, bound in enumerate(pruning_bounds):
        try:
            bounds[i] = float(bound)
        except ValueError:
            continue

    print(bounds)

    results = run_mockdown_timeout(input_data, options=dict(
        input_format=input_format,
        numeric_type=numeric_type,
        instantiation_method=instantiation_method,
        learning_method=learning_method,
        pruning_method=pruning_method,
        pruning_bounds=tuple(bounds),
        debug_noise=debug_noise,
        debug_visibilities=debug_visibilities,
        debug_instantiation=debug_instantiation,
        num_examples=num_examples
    ), timeout=timeout)

    click.echo(json.dumps(
        results,
        ensure_ascii=False,
        indent=2,
    ), file=output)


@click.command()
@click.argument('url')
@click.argument('output', type=click.File('w'))
@click.option('-r', '--root',
              type=str,
              default="body",
              show_default=True,
              help="Selector for the root element from which to begin scraping.")
@click.option('-d', '--dims',
              nargs=2,
              type=int,
              default=[1280, 800],
              show_default=True,
              help="Window dimensions to scrape at.")
def scrape(url: str, output: TextIO, root: str, dims: Tuple[int, int]) -> None:
    scraper = Scraper()
    results = scraper.scrape(url, dims, root_selector=root)
    scraper.cleanup()

    click.echo(json.dumps(
        results,
        ensure_ascii=False,
        indent=2,
    ), file=output)


@click.command()
@click.argument('input', type=click.File('r'))
def display(input: TextIO) -> None:
    import seaborn as sns

    # Load view JSON.
    input_data: dict = json.load(input)
    input.close()

    loader = PackageLoader('mockdown.display', 'templates')
    env = Environment(
        loader=loader,
        autoescape=select_autoescape(['html', 'xml'])
    )

    # Kind of a hack. Using importlib.resources is probably more Pythonic but...
    kiwi_js_src = loader.get_source(env, 'js/flightlessbird.all.js')[0]

    input_meta = input_data.get('meta', {})
    scrape_meta = input_data.get('scrape', {})

    # Utility for convenience.
    # todo: move elsewhere
    def get_meta(*keys: str, subject=input_meta, default=None):
        if len(keys) == 0:
            return input_meta

        k, ks = keys[0], keys[1:]
        result = input_meta.get(k, default)

        if not ks:
            return result
        else:
            return get_meta(*ks, subject=result, default=default)

    examples = input_data['examples']

    observed_bounds = {
        'min_width': min(e['rect'][2] - e['rect'][0] for e in examples),
        'max_width': max(e['rect'][2] - e['rect'][0] for e in examples),
        'min_height': min(e['rect'][3] - e['rect'][1] for e in examples),
        'max_height': max(e['rect'][3] - e['rect'][1] for e in examples),
    }

    context = {
        'examples': examples,
        'origin': get_meta('scrape', 'origin', default=None),
        'colors': sns.color_palette('bright', len(examples)).as_hex(),
        **observed_bounds
    }

    template = env.get_template('default.html.jinja2')
    html = template.render(**context)

    # Write the result to a temporary file, and open it in the user's web browser.
    tmp = tempfile.NamedTemporaryFile(mode='w', prefix='fnord-', suffix='.html', delete=False)
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
cli.add_command(scrape)

if __name__ == '__main__':
    cli()
