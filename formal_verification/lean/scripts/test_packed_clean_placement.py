"""Check native placement order and reject references absent from the bank."""
from unittest.mock import patch
import unittest

import gkr_clean_placement as placement


class CleanPlacementTests(unittest.TestCase):
    def test_constructor_codes_stay_distinct(self):
        addresses = [{"BaseLayerWitness": 0}, {"BaseLayerMemory": 0},
                     {"InnerLayer": {"layer": 0, "offset": 0}}, {"Setup": 0},
                     {"VirtualSetup": "RangeCheck16Bits"}, {"ScratchSpace": 0},
                     {"Cached": {"layer": 0, "offset": 0}}]
        self.assertEqual(list(map(placement.address_code, addresses)), [0, 2, 6, 12, 20, 30, 42])

    def test_coordinates_follow_the_bank_not_logical_keys(self):
        witness, memory = {"BaseLayerWitness": 0}, {"BaseLayerMemory": 1}
        pair = {"circuit": {"placement_data": {"1": memory, "0": witness}}}
        with patch.object(placement, "full_arithmetic", return_value={"addresses": [memory, witness]}):
            _, source = placement.module("fixture", "Fixture", pair, {})
        self.assertIn("references : List (Nat × Nat) := [(0, 1), (3, 0)]", source)
        self.assertIn("placements : List GKRAddress := [(.BaseLayerWitness 0), (.BaseLayerMemory 1)]", source)
        self.assertIn("native.addresses.map AddressUniqueChecks.addressCode", source)
        self.assertIn("references.map Prod.fst = placements.map AddressUniqueChecks.addressCode", source)
        self.assertNotIn("maxHeartbeats", source)

    def test_missing_native_coordinate_stops_generation(self):
        pair = {"circuit": {"placement_data": {"0": {"BaseLayerWitness": 1}}}}
        with patch.object(placement, "full_arithmetic", return_value={"addresses": [{"BaseLayerWitness": 0}]}):
            with self.assertRaises(KeyError):
                placement.module("fixture", "Fixture", pair, {})


if __name__ == "__main__":
    unittest.main()
