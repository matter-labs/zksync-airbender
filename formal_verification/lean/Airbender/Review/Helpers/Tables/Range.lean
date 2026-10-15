import Airbender.Review.Helpers.Core.Word
import Clean.Circuit.Operations
import Mathlib.Algebra.Field.ZMod
import Airbender.Import.SetupEmbed

namespace Airbender.Verification
open Airbender.Arithmetic

import_setup_range importedRange16 from "artifacts/setup/add-sub.json" virtual_range_bits 16
import_setup_range importedTimestamp19 from "artifacts/setup/add-sub.json" virtual_range_bits 19
import_setup_table importedRange13 from "artifacts/setup/bigint.json" native_table_id 26 select_native_columns [0]

/-- Actual exported virtual setup, including its native zero padding. -/
def range16Table {p : Nat} [Fact p.Prime] : Table (ZMod p) field :=
  importedRange16.scalarTable "Airbender.Range16"

/-- Actual bigint table ID 26, projected from its exported native region. -/
def range13Table {p : Nat} [Fact p.Prime] : Table (ZMod p) field :=
  importedRange13.scalarTable "Airbender.Range13"

/-- A native Clean query into the fixed range table; no prover-supplied table contents. -/
def range16 {p : Nat} [Fact p.Prime] (entry : Expression (ZMod p)) : Lookup (ZMod p) where
  table := range16Table.toRaw
  entry := #v[entry]

def range13 {p : Nat} [Fact p.Prime] (entry : Expression (ZMod p)) : Lookup (ZMod p) where
  table := range13Table.toRaw
  entry := #v[entry]

end Airbender.Verification
