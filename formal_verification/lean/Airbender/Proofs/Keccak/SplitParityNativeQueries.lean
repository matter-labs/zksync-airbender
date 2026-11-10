import Airbender.Proofs.Keccak.SplitParityGenericMembers
import Airbender.Review.Circuits.Keccak.SplitColumnParity
import Airbender.Review.Circuits.Keccak.SplitColumnParityCached
import Airbender.Proofs.Constraints
import Airbender.Review.Helpers.Properties

namespace Airbender.Keccak.Split.Native.Proofs
set_option warningAsError true
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
variable [Fact babyBearModulus.Prime]

/-- The retained complete physical native generic setup. -/
def columnParityFixedTable : Table (ZMod babyBearModulus) (fields 8) := Fixed.columnParityGenericTable

/-- All twenty-two actual generic lookups, in their native order. -/
def columnParityQuery (cached : Bool) (index : Fin 22) : Lookup (ZMod babyBearModulus) :=
  match cached with
  | false => (FlatOperation.lookups (ColumnParity.importedConstraints columnParityFixedTable)).get
      ⟨index.val, by change index.val < 22; exact index.isLt⟩
  | true => (FlatOperation.lookups (ColumnParityCached.importedConstraints columnParityFixedTable)).get
      ⟨index.val, by change index.val < 22; exact index.isLt⟩

theorem column_parity_query_table (cached : Bool) (index : Fin 22) :
    (columnParityQuery cached index).table = columnParityFixedTable.toRaw := by
  cases cached <;> fin_cases index <;> rfl

theorem column_parity_query_arity (cached : Bool) (index : Fin 22) :
    (columnParityQuery cached index).table.arity = 8 := by
  rw [column_parity_query_table]
  rfl

def columnParityQueryEntry (cached : Bool) (index : Fin 22) :
    Vector (Expression (ZMod babyBearModulus)) 8 :=
  (columnParityQuery cached index).entry.cast (column_parity_query_arity cached index)

theorem column_parity_query_shape (cached : Bool) (index : Fin 22) :
    columnParityQuery cached index = Lookup.mk columnParityFixedTable.toRaw (columnParityQueryEntry cached index) := by
  cases cached <;> fin_cases index <;> rfl

/-- Native fixed discriminators distinguish both controllers and both arithmetic regions. -/
def columnParityQueryTag (index : Fin 22) : Nat :=
  if index.val = 0 then 62 else if index.val = 1 then 63 else if index.val < 6 then 38 else 64

theorem column_parity_query_tag (cached : Bool) (index : Fin 22) (w : Nat → ZMod babyBearModulus) :
    (columnParityQueryEntry cached index)[7].eval (Verification.environment w) =
      (columnParityQueryTag index : ZMod babyBearModulus) := by
  cases cached <;> fin_cases index <;> rfl

/-- Satisfaction of either complete native capture enforces every actual generic query. -/
theorem column_parity_native_query (cached : Bool) (w : Nat → ZMod babyBearModulus)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (if cached then ColumnParityCached.clockConstraints columnParityFixedTable
        else ColumnParity.clockConstraints columnParityFixedTable))
    (index : Fin 22) : Fixed.columnParityGenericTable.toRaw.Soundness #[]
      ((columnParityQueryEntry cached index).map (Expression.eval (Verification.environment w))) := by
  have member : (columnParityQuery cached index).Contains (Verification.environment w) := by
    cases cached
    · exact Verification.lookup_of_holds (Verification.holds_of_sublist holds
        (List.sublist_append_left _ _)) ⟨index.val, by change index.val < 22; exact index.isLt⟩
    · exact Verification.lookup_of_holds (Verification.holds_of_sublist holds
        (List.sublist_append_left _ _)) ⟨index.val, by change index.val < 22; exact index.isLt⟩
  rw [column_parity_query_shape] at member
  exact (Lookup.mk columnParityFixedTable.toRaw (columnParityQueryEntry cached index)).table.imply_soundness _ _ member

/-- Each actual iota query has bounded bytes and its exact native round-constant output. -/
theorem column_parity_native_iota_queries (cached : Bool) (w : Nat → ZMod babyBearModulus)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (if cached then ColumnParityCached.clockConstraints columnParityFixedTable
        else ColumnParity.clockConstraints columnParityFixedTable)) (index : Fin 4) :
    let row := (columnParityQueryEntry cached ⟨2 + index.val, by omega⟩).map
      (Expression.eval (Verification.environment w))
    row[0].val < 256 ∧ row[1].val < 256 ∧ row[2].val < 256 ∧
      row[2].val = row[0].val ^^^ Airbender.Keccak.iotaByte row[1].val := by
  let query : Fin 22 := ⟨2 + index.val, by omega⟩
  have sound := column_parity_native_query cached w holds query
  have tag : (((columnParityQueryEntry cached query).map
      (Expression.eval (Verification.environment w)))[7]) = 38 := by
    have native := column_parity_query_tag cached query w
    have selected : columnParityQueryTag query = 38 := by fin_cases index <;> rfl
    simpa only [Vector.getElem_map, selected, Nat.cast_ofNat] using native
  exact Fixed.Proofs.column_parity_iota_table_sound _ ((Fixed.Proofs.column_parity_generic_bindings _ sound).1 tag)

/-- All sixteen actual parity queries enforce the exact five-input nibble operation. -/
theorem column_parity_native_xor5_queries (cached : Bool) (w : Nat → ZMod babyBearModulus)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (if cached then ColumnParityCached.clockConstraints columnParityFixedTable
        else ColumnParity.clockConstraints columnParityFixedTable)) (index : Fin 16) :
    let row := (columnParityQueryEntry cached ⟨6 + index.val, by omega⟩).map
      (Expression.eval (Verification.environment w))
    (∀ column : Fin 5, row[column.val].val < 16) ∧ row[5].val < 16 ∧
      row[5].val = row[0].val ^^^ row[1].val ^^^ row[2].val ^^^ row[3].val ^^^ row[4].val ∧
      row[6] = 0 ∧ row[7] = 64 := by
  let query : Fin 22 := ⟨6 + index.val, by omega⟩
  have sound := column_parity_native_query cached w holds query
  have tag : (((columnParityQueryEntry cached query).map
      (Expression.eval (Verification.environment w)))[7]) = 64 := by
    have native := column_parity_query_tag cached query w
    have selected : columnParityQueryTag query = 64 := by fin_cases index <;> rfl
    simpa only [Vector.getElem_map, selected, Nat.cast_ofNat] using native
  exact Fixed.Proofs.xor5_table_sound _ ((Fixed.Proofs.column_parity_generic_bindings _ sound).2.2.2 tag)

end Airbender.Keccak.Split.Native.Proofs
