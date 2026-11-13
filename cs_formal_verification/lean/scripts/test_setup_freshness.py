"""A changed native setup row must fail freshness."""
import json
from pathlib import Path
import tempfile
import unittest
from check_setup_freshness import compare_artifact


class SetupFreshnessTest(unittest.TestCase):
    def test_complete_payload_is_compared(self):
        with tempfile.TemporaryDirectory() as directory:
            expected, fresh = [Path(directory) / name for name in ['expected.json', 'fresh.json']]
            expected.write_text('{"columns":[{"values":[0,1,2]}]}')
            fresh.write_text(json.dumps(json.loads(expected.read_text()), indent=2))
            compare_artifact(fresh, expected)
            fresh.write_text('{"columns":[{"values":[0,9,2]}]}')
            with self.assertRaisesRegex(ValueError, 'Native setup differs'):
                compare_artifact(fresh, expected)


if __name__ == '__main__':
    unittest.main()
