"""Check complete native coverage, signed metadata and safe shard retirement."""
from pathlib import Path
from tempfile import TemporaryDirectory
from unittest.mock import patch
import unittest

import generate_packed_xor9 as generator


class PackedXor9Tests(unittest.TestCase):
    def fixture(self):
        block = {'kind': 'affine', 'length': 262144, 'first': 1, 'step': -1}
        return {'tables': [{'id': 20, 'offset': 0, 'length': 262144, 'width': 3, 'key_columns': 2}],
                'columns': [{}, {}, {'blocks': [block]}]}

    def test_signed_constructor_and_word_order(self):
        self.assertEqual(generator.term({'kind': 'affine', 'length': 2, 'first': 511, 'step': -1}),
                         '(.affine 2 511 (-1))')
        self.assertEqual(generator.pack([511, 1]), 66047)
        with self.assertRaises(ValueError):
            generator.pack([65536])

    def test_reject_incomplete_or_changed_region(self):
        artifact = self.fixture()
        self.assertEqual(len(generator.native_blocks(artifact)), 1)
        artifact['columns'][2]['blocks'][0]['length'] -= 1
        with self.assertRaisesRegex(ValueError, 'cover'):
            generator.native_blocks(artifact)
        artifact['tables'][0]['width'] = 4
        with self.assertRaisesRegex(ValueError, 'dimensions'):
            generator.native_blocks(artifact)

    def test_reject_cut_native_block(self):
        artifact = self.fixture()
        artifact['tables'][0]['offset'] = 1
        artifact['columns'][2]['blocks'][0]['length'] += 1
        with self.assertRaisesRegex(ValueError, 'boundary'):
            generator.native_blocks(artifact)

    def test_keep_untracked_file_at_retired_path(self):
        with TemporaryDirectory() as directory:
            root = Path(directory)
            path = root / generator.retired()[0]
            path.parent.mkdir(parents=True)
            path.write_text('unrelated\n')
            with patch.object(generator.subprocess, 'run') as run:
                run.return_value.returncode = 1
                generator.write_or_check(root, {}, True)
            self.assertEqual(path.read_text(), 'unrelated\n')


if __name__ == '__main__':
    unittest.main()
