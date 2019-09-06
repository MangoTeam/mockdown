import click
import uvicorn

from mockdown.app import app


@click.command()
def cli():
    click.echo("Starting mockdown...")
    uvicorn.run(app, host='0.0.0.0', port=8000)
