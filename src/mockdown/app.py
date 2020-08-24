import logging
import os
from typing import Any, Dict, Optional

from starlette.applications import Starlette
from starlette.middleware.cors import CORSMiddleware
from starlette.requests import Request
from starlette.responses import JSONResponse
from starlette.staticfiles import StaticFiles
from mockdown.run import run_timeout as run_mockdown_timeout

logger = logging.getLogger(__name__)


async def synthesize(request: Request) -> JSONResponse:
    request_json = await request.json()

    options = request_json.pop('options', {})
    timeout = request_json.pop('timeout', None)
    input_data = request_json
    # print(input_data)

    logger.info("===== SYNTH START =====")
    result = run_mockdown_timeout(input_data, options=options, timeout=timeout)
    logger.info("===== SYNTH END =======")
    if result:
        return JSONResponse(result)
    else:
        raise Exception('timeout')


def create_app(*, static_dir: Optional[str] = None, static_path: Optional[str] = None,
               **_kwargs: Dict[str, Any]) -> Starlette:
    app = Starlette(debug=True)
    app.add_middleware(CORSMiddleware, allow_origins=['*'], allow_methods=['*'], allow_headers=['*'],
                       allow_credentials=True)
    app.add_route('/api/synthesize', synthesize, methods=['POST'])
    if static_dir is not None and static_path is not None:
        app.mount(static_path, app=StaticFiles(directory=static_dir), name='static')

    # if os.name != 'nt':
    #     from timing_asgi import TimingClient, TimingMiddleware  # type: ignore
    #     from timing_asgi.integrations import StarletteScopeToName  # type: ignore
    #
    #     class StdoutTimingClient(TimingClient):  # type: ignore
    #         def timing(self, metric_name, timing, tags=None) -> None:  # type: ignore
    #             print(metric_name, timing, tags)
    #
    #     app.add_middleware(
    #         TimingMiddleware,
    #         client=StdoutTimingClient(),
    #         metric_namer=StarletteScopeToName(prefix="mockdown", starlette_app=app)
    #     )

    return app


default_app = create_app()
