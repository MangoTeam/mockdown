# Adapted from https://gist.github.com/gyglim/54ebb90f7fc93417cf15ebd2c9abc97a

import sys
import threading

from multiprocessing import TimeoutError
from queue import Queue


def with_timeout(max_time):
    def timeout_decorator(fn):
        def wrapper(*args, **kwargs):
            queue = Queue()

            def enqueue_fn():
                try:  # Try adding the results of the function call
                    queue.put(fn(*args, **kwargs))
                except BaseException:
                    # If it fails, enqueue the exception instead.
                    queue.put(sys.exc_info())

            thread = threading.Thread(target=enqueue_fn)
            thread.start()
            thread.join(max_time)

            if thread.isAlive():
                raise TimeoutError("Processing took longer than %s seconds" % max_time)

            output = queue.get_nowait()
            # Reraise if an exception occured
            if isinstance(output, tuple) and type(output[0]) is type and isinstance(output[0](), BaseException):
                raise (output[0], output[1], output[2])
            else:  # return the results otherwise
                return output

        return wrapper

    # Return the timeout decorator
    return timeout_decorator
