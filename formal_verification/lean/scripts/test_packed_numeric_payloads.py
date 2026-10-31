"""Keep numeric payloads bound to their native sources and complete dimensions."""
import json
from pathlib import Path
from tempfile import TemporaryDirectory
import unittest

import gkr_numeric_arithmetic as numeric


class NumericPayloadTests(unittest.TestCase):
    def fixture(self, root):
        name = "blake-round-cached"
        selectors = {"inputs": [0], "addresses": [0, 1],
                     "counts": {"source_obligations": 1, "relations": 1}}
        for relative in [f"artifacts/compiler/{name}.json", f"artifacts/compiler/{name}-source.json",
                         "Airbender/Import/GKRProtocol/FullArithmeticImport.lean"]:
            path = root / relative
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text("original\n")
        raw = {"source": [[(1, [0])]], "lowered": [[(1, [0])]], "extension": [[]],
               "backward": [[([], 0)]], "forward": [[([], 0)]],
               "gateInput": [[]], "gateOutput": [[]], "keys": [1, 0]}
        payload = numeric.prepare_payload(root, name, selectors, raw)
        path = numeric.payload_path(root, name)
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(json.dumps(payload))
        return name, selectors, payload, path

    def test_source_and_selector_drift_rejected(self):
        with TemporaryDirectory() as directory:
            root = Path(directory)
            name, selectors, _, _ = self.fixture(root)
            numeric.check_payload(root, name, selectors)
            changed = {**selectors, "inputs": [2]}
            with self.assertRaisesRegex(ValueError, "provenance changed"):
                numeric.check_payload(root, name, changed)
            (root / f"artifacts/compiler/{name}.json").write_text("changed\n")
            with self.assertRaisesRegex(ValueError, "provenance changed"):
                numeric.check_payload(root, name, selectors)

    def test_missing_rows_and_fields_rejected(self):
        with TemporaryDirectory() as directory:
            root = Path(directory)
            name, selectors, payload, path = self.fixture(root)
            payload["backward"] = []
            path.write_text(json.dumps(payload))
            with self.assertRaisesRegex(ValueError, "row count changed"):
                numeric.check_payload(root, name, selectors)
            del payload["gateOutputNormalized"]
            path.write_text(json.dumps(payload))
            with self.assertRaisesRegex(ValueError, "field set changed"):
                numeric.check_payload(root, name, selectors)

    def test_normalization_preserves_modular_polynomial(self):
        self.assertEqual(numeric.normalize([[1, [1, 0]], [numeric.PRIME - 1, [0, 1]],
                                            [2, []], [numeric.PRIME - 2, []], [3, [2]]]),
                         [[3, [2]]])


if __name__ == "__main__":
    unittest.main()
