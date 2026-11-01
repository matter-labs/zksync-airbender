"""Check packed word boundaries, complete traces and source-bound payloads."""
import unittest

import gkr_dense_arithmetic as dense


class DenseArithmeticTests(unittest.TestCase):
    def test_packed_words_preserve_all_terms(self):
        row = [[0, []], [dense.COEFFICIENT - 1, [510, 0]], [1, [2]]]
        count, value = dense.pack(row)
        decoded = []
        for _ in range(count):
            word, value = value % dense.WORD, value // dense.WORD
            decoded.append((word % dense.COEFFICIENT, word // dense.COEFFICIENT))
        self.assertEqual(decoded, [(0, 0), (dense.COEFFICIENT - 1, 512), (1, 1025)])
        self.assertEqual(value, 0)

    def test_out_of_bound_terms_rejected(self):
        for row in [[[dense.COEFFICIENT, []]], [[1, [0, 511]]], [[1, [0, 1, 2]]]]:
            with self.assertRaises(ValueError):
                dense.pack(row)

    def test_trace_retains_zero_and_wrap_steps(self):
        row = [[0, [3]], [1, [0]], [dense.PRIME - 1, [0]], [2, []]]
        trace = dense.trace_row([[2, []]], row)
        self.assertEqual(trace["input"][0], 4)
        self.assertEqual(len(trace["trace"]), 5)
        self.assertEqual(trace["trace"][0][1], trace["expected"])
        self.assertEqual(trace["trace"][-1], [0, [0, 0]])


if __name__ == "__main__":
    unittest.main()
