import Human.Helpers.Core.Word
import Clean.Circuit.Operations
import Mathlib.Algebra.Field.ZMod

namespace Airbender.Verification
open Airbender.Arithmetic

/-- Native Clean static range semantics, shared by the 16-bit and 13-bit tables. -/
def rangeTable {p : Nat} [Fact p.Prime] (name : String) (bound : Nat) : Table (ZMod p) field := .fromStatic {
  name := name
  length := bound
  row i := (i.val : ZMod p)
  index x := x.val
  Spec x := x.val < bound
  contains_iff := by
    intro x
    constructor
    · rintro ⟨i, rfl⟩
      exact lt_of_le_of_lt (by simp only [ZMod.val_natCast]; exact Nat.mod_le _ _) i.isLt
    · intro h
      exact ⟨⟨x.val, h⟩, (ZMod.natCast_zmod_val x).symm⟩
}

/-- Handwritten reconstruction of Airbender's fixed 16-bit table; Clean supplies
    the lookup semantics. Source: `materialize_virtual_range_check_setup_poly` in
    `prover/src/gkr/virtual_polys/range_check.rs`, instantiated with 16 bits in
    `prover/src/gkr/prover/mod.rs` for `VirtualSetupPoly::RangeCheck16Bits`.
    The importer binds JSON `range_check_16_lookup_expressions` to this table.
    Rust's extra zero padding does not change the set of permitted values.
    Faithfulness to the Rust setup and this query binding remain unproved. -/
def range16Table {p : Nat} [Fact p.Prime] : Table (ZMod p) field :=
  rangeTable "Airbender.Range16" limbBase

/-- Rust's `RangeCheck13`, table ID 26. Its setup correspondence is unproved. -/
def range13Table {p : Nat} [Fact p.Prime] : Table (ZMod p) field :=
  rangeTable "Airbender.Range13" 8192

/-- A native Clean query into the fixed range table; no prover-supplied table contents. -/
def range16 {p : Nat} [Fact p.Prime] (entry : Expression (ZMod p)) : Lookup (ZMod p) where
  table := range16Table.toRaw
  entry := #v[entry]

def range13 {p : Nat} [Fact p.Prime] (entry : Expression (ZMod p)) : Lookup (ZMod p) where
  table := range13Table.toRaw
  entry := #v[entry]

end Airbender.Verification
