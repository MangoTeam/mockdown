from mockdown.model import ZViewLoader


class TestZViewLoader:
    def test_strictly_ints(self) -> None:
        loader = ZViewLoader(integerize_fn=ZViewLoader.strictly_ints)
