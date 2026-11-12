module
public import Human.Helpers.Core.Word
public import CleanCore.Circuit.Operations
public import Mathlib.Algebra.Field.ZMod

@[expose] public section

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

/-- Native 16-bit range. Every imported setup checks its complete increasing
    prefix and zero padding with `check_native_ranges`. Padding adds only zero. -/
def range16Table {p : Nat} [Fact p.Prime] : Table (ZMod p) field :=
  rangeTable "Airbender.Range16" limbBase

/-- Native `RangeCheck13`, table ID 26. The comparison below checks every row. -/
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
