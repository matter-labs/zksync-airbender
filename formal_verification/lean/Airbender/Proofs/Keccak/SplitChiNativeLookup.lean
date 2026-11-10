import Airbender.Proofs.Keccak.SplitChiLookup
import Airbender.Review.Circuits.Keccak.SplitChi5
import Airbender.Review.Circuits.Keccak.SplitChi5Cached
import Airbender.Proofs.Constraints
import Airbender.Review.Helpers.Properties

namespace Airbender.Keccak.Split.Native.Proofs
open Airbender.Setup
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 1600000
variable [Fact babyBearModulus.Prime]

/-- The retained complete native chi5 generic table. -/
def chi5FixedTable : Table (ZMod babyBearModulus) (fields 11) :=
  Fixed.chi5Generic.table "Airbender.SplitChi5Generic"

/-- The sixteen arithmetic lookups follow the native controller lookup. -/
def chi5ArithmeticQuery (cached : Bool) (index : Fin 16) : Lookup (ZMod babyBearModulus) :=
  match cached with
  | false => (FlatOperation.lookups (Chi5.importedConstraints chi5FixedTable)).get
      ⟨1 + index.val, by change 1 + index.val < 17; omega⟩
  | true => (FlatOperation.lookups (Chi5Cached.importedConstraints chi5FixedTable)).get
      ⟨1 + index.val, by change 1 + index.val < 17; omega⟩

theorem chi5_arithmetic_table (cached : Bool) (index : Fin 16) :
    (chi5ArithmeticQuery cached index).table = chi5FixedTable.toRaw := by
  cases cached <;> fin_cases index <;> rfl

theorem chi5_arithmetic_arity (cached : Bool) (index : Fin 16) :
    (chi5ArithmeticQuery cached index).table.arity = 11 := by
  rw [chi5_arithmetic_table]
  rfl

def chi5ArithmeticEntry (cached : Bool) (index : Fin 16) :
    Vector (Expression (ZMod babyBearModulus)) 11 :=
  (chi5ArithmeticQuery cached index).entry.cast (chi5_arithmetic_arity cached index)

theorem chi5_arithmetic_query_shape (cached : Bool) (index : Fin 16) :
    chi5ArithmeticQuery cached index = Lookup.mk chi5FixedTable.toRaw (chi5ArithmeticEntry cached index) := by
  cases cached <;> fin_cases index <;> rfl

/-- Each actual arithmetic query retains its complete constant native table tag. -/
theorem chi5_arithmetic_tag (cached : Bool) (index : Fin 16)
    (w : Nat → ZMod babyBearModulus) :
    (chi5ArithmeticEntry cached index)[10].eval (Verification.environment w) = 65 := by
  cases cached <;> fin_cases index <;> rfl

/-- Both native cache modes enforce the exact chi operation on every queried nibble. -/
theorem chi5_native_arithmetic_queries (cached : Bool) (w : Nat → ZMod babyBearModulus)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (if cached then Chi5Cached.clockConstraints chi5FixedTable else Chi5.clockConstraints chi5FixedTable))
    (index : Fin 16) :
    let row := (chi5ArithmeticEntry cached index).map (Expression.eval (Verification.environment w))
    (∀ column : Fin 5, row[column.val].val < 16) ∧
    (∀ column : Fin 5, row[5 + column.val].val < 16 ∧
      row[5 + column.val].val = row[column.val].val ^^^
        ((15 ^^^ row[(column.val + 1) % 5].val) &&& row[(column.val + 2) % 5].val)) := by
  have member : (chi5ArithmeticQuery cached index).Contains (Verification.environment w) := by
    cases cached
    · have core := Verification.holds_of_sublist holds
        (List.sublist_append_left (Chi5.importedConstraints chi5FixedTable) Chi5.importedConstraintsTimestampLookups)
      exact Verification.lookup_of_holds core ⟨1 + index.val, by change 1 + index.val < 17; omega⟩
    · have core := Verification.holds_of_sublist holds
        (List.sublist_append_left (Chi5Cached.importedConstraints chi5FixedTable) Chi5Cached.importedConstraintsTimestampLookups)
      exact Verification.lookup_of_holds core ⟨1 + index.val, by change 1 + index.val < 17; omega⟩
  rw [chi5_arithmetic_query_shape] at member
  have sound := (Lookup.mk chi5FixedTable.toRaw (chi5ArithmeticEntry cached index)).table.imply_soundness _ _ member
  exact Fixed.Proofs.chi5_generic_lookup_sound _ sound
    (by simpa only [Vector.getElem_map] using chi5_arithmetic_tag cached index w)

end Airbender.Keccak.Split.Native.Proofs
