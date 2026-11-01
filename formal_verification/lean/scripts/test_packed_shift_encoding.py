"""Controls for the shift encoding generator. Lean checks the native bindings."""
import unittest

from generate_shift_packed_encoding import native_blocks, payload


def artifact(blocks, offset=1, length=262144):
    return {'tables': [{'id': 9, 'length': length, 'width': 8,
                        'key_columns': 4, 'offset': offset}],
            'columns': [{'blocks': blocks} for _ in range(8)]}


class ShiftEncodingTests(unittest.TestCase):
    def test_clipped_affine_region(self):
        blocks = [{'kind': 'affine', 'length': 262146, 'first': 7, 'step': 0}]
        self.assertEqual(native_blocks(artifact(blocks), 0),
                         [{'kind': 'affine', 'length': 262144, 'first': 7, 'step': 0}])

    def test_dimension_change_rejected(self):
        with self.assertRaisesRegex(ValueError, 'dimensions'):
            native_blocks(artifact([], length=262143), 0)

    def test_missing_rows_rejected(self):
        with self.assertRaisesRegex(ValueError, 'incomplete'):
            native_blocks(artifact([]), 0)

    def test_signed_payload(self):
        self.assertEqual(int(payload([{'kind': 'affine', 'length': 3,
                                       'first': 2, 'step': -1}]), 0), 2 + 65536)

    def test_nonbyte_rejected(self):
        for value in [-1, 256]:
            with self.assertRaisesRegex(ValueError, 'byte'):
                payload([{'kind': 'dense', 'values': [value]}])


if __name__ == '__main__':
    unittest.main()
