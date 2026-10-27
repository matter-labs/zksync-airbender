import json
from pathlib import Path
import tempfile
import unittest

from check_olean_hashes import verify


class ArtifactHashTests(unittest.TestCase):
    def test_recomputed_hash_must_match_trace_even_if_sidecar_was_refreshed(self):
        with tempfile.TemporaryDirectory() as directory:
            path = str(Path(directory) / 'Fixture.olean')
            Path(path).with_suffix('.trace').write_text(json.dumps({'outputs': {'o': ['1111111111111111.olean']}}))
            Path(path + '.hash').write_text('1111111111111111')
            verify([path], [{'path': path, 'hash': '1111111111111111'}])
            Path(path + '.hash').write_text('2222222222222222')
            with self.assertRaisesRegex(ValueError, 'differs from its Lake trace'):
                verify([path], [{'path': path, 'hash': '2222222222222222'}])

    def test_missing_or_duplicate_recomputed_files_are_rejected(self):
        with self.assertRaisesRegex(ValueError, 'inventory'):
            verify(['missing.olean'], [])
        with self.assertRaisesRegex(ValueError, 'Duplicate'):
            verify([], [{'path': 'x', 'hash': '1'}, {'path': 'x', 'hash': '1'}])

    def test_each_module_part_has_its_own_recorded_output(self):
        with tempfile.TemporaryDirectory() as directory:
            base = str(Path(directory) / 'Fixture')
            suffixes = ('.olean', '.olean.server', '.olean.private')
            hashes = ('1111111111111111', '2222222222222222', '3333333333333333')
            Path(base + '.trace').write_text(json.dumps({'outputs': {'o': [
                value + suffix for suffix, value in zip(suffixes, hashes)]}}))
            paths = [base + suffix for suffix in suffixes]
            reports = [{'path': path, 'hash': value} for path, value in zip(paths, hashes)]
            verify(paths, reports)
            for index in range(3):
                with self.subTest(part=suffixes[index]):
                    changed = [dict(record) for record in reports]
                    changed[index]['hash'] = 'ffffffffffffffff'
                    with self.assertRaisesRegex(ValueError, 'differs from its Lake trace'):
                        verify(paths, changed)


if __name__ == '__main__':
    unittest.main()
