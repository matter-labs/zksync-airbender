"""Check complete Chi coverage and reject native boundary or dimension changes."""
import unittest

import generate_packed_chi as generator


class PackedChiTests(unittest.TestCase):
    def fixture(self):
        return {'tables': [{'id': 39, 'offset': 0, 'length': 65536, 'width': 3, 'key_columns': 2}],
                'columns': [{}, {}, {'blocks': [{'kind': 'affine', 'length': 65536, 'first': 0, 'step': 0}]}]}

    def test_complete_coverage(self):
        artifact = self.fixture()
        self.assertEqual(len(generator.native_blocks(artifact)), 1)
        artifact['columns'][2]['blocks'][0]['length'] -= 1
        with self.assertRaisesRegex(ValueError, 'cover'):
            generator.native_blocks(artifact)

    def test_changed_dimensions(self):
        artifact = self.fixture()
        artifact['tables'][0]['width'] = 4
        with self.assertRaisesRegex(ValueError, 'dimensions'):
            generator.native_blocks(artifact)

    def test_cut_source_block(self):
        artifact = self.fixture()
        artifact['tables'][0]['offset'] = 1
        artifact['columns'][2]['blocks'][0]['length'] += 1
        with self.assertRaisesRegex(ValueError, 'boundary'):
            generator.native_blocks(artifact)


if __name__ == '__main__':
    unittest.main()
