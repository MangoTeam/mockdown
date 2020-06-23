import io
import json
from typing import Any, Dict

from starlette.applications import Starlette
from starlette.middleware.cors import CORSMiddleware
from starlette.requests import Request
from starlette.responses import JSONResponse
from starlette.staticfiles import StaticFiles
from timing_asgi import TimingClient, TimingMiddleware  # type: ignore
from timing_asgi.integrations import StarletteScopeToName  # type: ignore

from mockdown.run import run as run_mockdown


async def synthesize(request: Request) -> JSONResponse:
    request_json = await request.json()

    # todo: move these into an `opts` object in the input json.
    opts = {
        'numeric_type': request_json.pop('numeric_type', 'N'),
        'pruning_method': request_json.pop('pruning', 'none')
    }

    # Kind of a hack, we rewrite the JSON back as a string, as that's whast
    # the cli.run interface expected (it expects a TextIO it can call json.load on)
    req_io = io.StringIO()
    json.dump(request_json, req_io)
    req_io.seek(0)

    result = run_mockdown(req_io, **opts)
    return JSONResponse(result)


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

# default_app = create_app(static_dir='static/', static_path='/')
