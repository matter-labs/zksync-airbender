#!/usr/bin/env python3
"""Test that the setup scan generator rejects loose configurations and loose slice plans."""
import copy
import unittest
from generate_setup_scans import check_partition, cut_block, cut_column, slices, validate


def native():
    """A setup of 64 rows and two columns: an affine column and a periodic column with period 4."""
    return {'trace_len': 64, 'columns': [
        {'blocks': [{'kind': 'affine', 'length': 64, 'first': 0, 'step': 1}]},
        {'blocks': [{'kind': 'dense', 'values': [1, 2, 3, 4]},
                    {'kind': 'periodic', 'repetitions': 15, 'stride': 1, 'values': [0, 1, 2, 3]}]},
    ]}


def setup(**changes):
    result = {'name': 'Example', 'columns': ['column0', 'column1'], 'per_row': [], 'long_cost': 8}
    result.update(changes)
    return result


class ValidateTests(unittest.TestCase):
    def test_valid_configuration(self):
        validate(setup(per_row=[(4, 12), (8, 16, (1,))], bitwise={1: (4, 64, [(1, 4)])}, cuts=[8, (12, (0,))]),
                 native())

    def test_column_count(self):
        with self.assertRaisesRegex(ValueError, 'native columns'):
            validate(setup(columns=['column0']), native())

    def test_unknown_per_row_column(self):
        with self.assertRaisesRegex(ValueError, 'names a column outside'):
            validate(setup(per_row=[(4, 12, (2,))]), native())

    def test_empty_per_row_columns(self):
        with self.assertRaisesRegex(ValueError, 'names a column outside'):
            validate(setup(per_row=[(4, 12, ())]), native())

    def test_reversed_per_row_range(self):
        with self.assertRaisesRegex(ValueError, 'empty, reversed or outside'):
            validate(setup(per_row=[(12, 4)]), native())

    def test_empty_per_row_range(self):
        with self.assertRaisesRegex(ValueError, 'empty, reversed or outside'):
            validate(setup(per_row=[(8, 8)]), native())

    def test_per_row_range_outside_trace(self):
        with self.assertRaisesRegex(ValueError, 'empty, reversed or outside'):
            validate(setup(per_row=[(60, 65)]), native())

    def test_per_row_bound_inside_period(self):
        with self.assertRaisesRegex(ValueError, 'inside a period'):
            validate(setup(per_row=[(4, 10, (1,))]), native())

    def test_unknown_bitwise_column(self):
        with self.assertRaisesRegex(ValueError, 'names a column outside'):
            validate(setup(bitwise={5: (0, 64, [(1, 4)])}), native())

    def test_reversed_bitwise_range(self):
        with self.assertRaisesRegex(ValueError, 'empty, reversed or outside'):
            validate(setup(bitwise={1: (64, 4, [(1, 4)])}), native())

    def test_bitwise_without_digits(self):
        with self.assertRaisesRegex(ValueError, 'no digits'):
            validate(setup(bitwise={1: (4, 64, [])}), native())

    def test_unknown_cut_column(self):
        with self.assertRaisesRegex(ValueError, 'names a column outside'):
            validate(setup(cuts=[(8, (3,))]), native())

    def test_cut_outside_trace(self):
        with self.assertRaisesRegex(ValueError, 'cut row'):
            validate(setup(cuts=[64]), native())


class CutTests(unittest.TestCase):
    def test_cut_inside_a_period_moves_to_its_bounds(self):
        pieces, chunks = cut_column(setup(cuts=[10]), 1, native()['columns'][1]['blocks'])
        self.assertEqual(chunks, [(0, [(1, [4, 4])], 0)])
        self.assertEqual([piece['repetitions'] for piece in pieces[1:]], [1, 1, 13])
        self.assertEqual(pieces[3]['values'], [2, 3, 4, 5])

    def test_cut_length_off_a_period_bound(self):
        with self.assertRaisesRegex(ValueError, 'on a period bound'):
            cut_block(native()['columns'][1]['blocks'][1], [6])

    def test_cut_of_a_dense_block(self):
        with self.assertRaisesRegex(ValueError, 'on a period bound'):
            cut_block(native()['columns'][1]['blocks'][0], [2])

    def test_cut_past_the_block(self):
        with self.assertRaisesRegex(ValueError, 'on a period bound'):
            cut_block(native()['columns'][0]['blocks'][0], [64])


class PartitionTests(unittest.TestCase):
    def setUp(self):
        self.columns = [column['blocks'] for column in native()['columns']]
        self.parts = slices(setup(), self.columns, 64)

    def test_complete_partition(self):
        check_partition(setup(), self.columns, 64, self.parts)

    def test_gap(self):
        parts = [part for part in self.parts if not (part[0] == 1 and part[1] == 0)]
        with self.assertRaisesRegex(ValueError, 'gap or overlap|slices end'):
            check_partition(setup(), self.columns, 64, parts)

    def test_overlap(self):
        parts = copy.deepcopy(self.parts)
        index = next(i for i, part in enumerate(parts) if part[0] == 1)
        parts.insert(index + 1, parts[index])
        with self.assertRaisesRegex(ValueError, 'gap or overlap'):
            check_partition(setup(), self.columns, 64, parts)

    def column1(self, *slices_of_column):
        """The plan with the slices of column 1 replaced by `slices_of_column` (first, count, start row, last row)."""
        return [part for part in self.parts if part[0] != 1] + [
            (1, first, count, [], start_row, last_row, 1) for first, count, start_row, last_row in slices_of_column]

    def test_split_partition(self):
        check_partition(setup(), self.columns, 64, self.column1((0, 1, 0, 4), (1, 1, 4, 64)))

    def test_unknown_column(self):
        for column in (2, -1):
            with self.assertRaisesRegex(ValueError, 'a slice names column'):
                check_partition(setup(), self.columns, 64, self.parts + [(column, 0, 1, [], 0, 64, 1)])

    def test_empty_slice(self):
        with self.assertRaisesRegex(ValueError, 'are empty or outside'):
            check_partition(setup(), self.columns, 64, self.column1((0, 0, 0, 0), (0, 2, 0, 64)))

    def test_blocks_outside_column(self):
        with self.assertRaisesRegex(ValueError, 'are empty or outside'):
            check_partition(setup(), self.columns, 64, self.column1((0, 3, 0, 64)))

    def test_rows_not_spanned(self):
        with self.assertRaisesRegex(ValueError, 'do not span'):
            check_partition(setup(), self.columns, 64, self.column1((0, 1, 0, 10), (1, 1, 10, 64)))

    def test_reversed_rows(self):
        with self.assertRaisesRegex(ValueError, 'do not span'):
            check_partition(setup(), self.columns, 64, self.column1((0, 1, 0, 70), (1, 1, 70, 64)))

    def test_short_trace(self):
        with self.assertRaisesRegex(ValueError, 'blocks cover'):
            slices(setup(), self.columns, 65)


if __name__ == '__main__':
    unittest.main()
