import Airbender.Review.Helpers.Core.Word
import Clean.Circuit.Operations
import Mathlib.Algebra.Field.ZMod

namespace Airbender.Verification

/-- Modeled native scalar range table. Binding to v2 setup generation is pending. -/
def rangeTable {p : Nat} [Fact p.Prime] (bits : Nat) : StaticTable (ZMod p) field where
  name := "Airbender.Range" ++ toString bits
  length := 2 ^ bits
  row i := (i.val : ZMod p)
  index x := x.val
  Spec x := x.val < 2 ^ bits
  contains_iff x := by
    constructor
    · rintro ⟨i, rfl⟩
      simpa only [ZMod.val_natCast] using lt_of_le_of_lt (Nat.mod_le i.val p) i.isLt
    · intro h
      exact ⟨⟨x.val, h⟩, (ZMod.natCast_zmod_val x).symm⟩

def range16Table {p : Nat} [Fact p.Prime] : Table (ZMod p) field :=
  (rangeTable 16).toTable

def range13Table {p : Nat} [Fact p.Prime] : Table (ZMod p) field :=
  (rangeTable 13).toTable

def range16 {p : Nat} [Fact p.Prime] (entry : Expression (ZMod p)) : Lookup (ZMod p) where
  table := range16Table.toRaw
  entry := #v[entry]

def range13 {p : Nat} [Fact p.Prime] (entry : Expression (ZMod p)) : Lookup (ZMod p) where
  table := range13Table.toRaw
  entry := #v[entry]

def timestamp19 {p : Nat} [Fact p.Prime] (entry : Expression (ZMod p)) : Lookup (ZMod p) where
  table := (rangeTable 19).toTable.toRaw
  entry := #v[entry]

end Airbender.Verification
