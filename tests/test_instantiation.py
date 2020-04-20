from pprint import pprint

from mockdown.instantiation import VisibilityConstraintInstantiator
from mockdown.model import ZViewLoader


class TestVisibilityConstraintInstantiator:
    def test_simple(self):
        loader = ZViewLoader(integerize_fn=ZViewLoader.strictly_ints)
        view = loader.load_dict({
            'name': 'root',
            'rect': [0, 0, 100, 100],
            'children': [{
                'name': 'child',
                'rect': [10, 10, 90, 90]
            }]
        })

        inst = VisibilityConstraintInstantiator()
        tpls = inst.instantiate([view])

        pprint("HI")
        pprint(tpls)