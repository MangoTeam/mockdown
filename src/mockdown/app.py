import logging
from typing import Any, Dict

from starlette.applications import Starlette
from starlette.middleware.cors import CORSMiddleware
from starlette.requests import Request
from starlette.responses import JSONResponse
from starlette.staticfiles import StaticFiles
from timing_asgi import TimingClient, TimingMiddleware  # type: ignore
from timing_asgi.integrations import StarletteScopeToName  # type: ignore

from mockdown.run import run_timeout as run_mockdown_timeout

logger = logging.getLogger(__name__)


async def synthesize(request: Request) -> JSONResponse:
    request_json = await request.json()

    options = request_json.pop('options', {})
    timeout = request_json.pop('timeout', None)
    input_data = request_json

    logger.info("===== SYNTH START =====")
    result = run_mockdown_timeout(input_data, options=options, timeout=timeout)
    logger.info("===== SYNTH END =======")
    if result:
        return JSONResponse(result)
    else:
        raise Exception('timeout')


def create_app(*, static_dir: str, static_path: str, **_kwargs: Dict[str, Any]) -> Starlette:
    app = Starlette(debug=True)
    app.add_middleware(CORSMiddleware, allow_origins=['*'], allow_methods=['*'], allow_headers=['*'],
                       allow_credentials=True)
    app.add_route('/api/synthesize', synthesize, methods=['POST'])
    app.mount(static_path, app=StaticFiles(directory=static_dir), name='static')

    class StdoutTimingClient(TimingClient):  # type: ignore
        def timing(self, metric_name, timing, tags=None) -> None:  # type: ignore
            print(metric_name, timing, tags)

    app.add_middleware(
        TimingMiddleware,
        client=StdoutTimingClient(),
        metric_namer=StarletteScopeToName(prefix="mockdown", starlette_app=app)
    )

    return app

# default_app = create_app(static_dir='static/', static_path='/')
