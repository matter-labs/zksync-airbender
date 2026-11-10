import Airbender.Proofs.Keccak.SplitParityNativeQueries

namespace Airbender.Keccak.Split.Native.Proofs
set_option warningAsError true
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
variable [Fact babyBearModulus.Prime]

/-- The complete evaluated fields of one actual parity query. -/
def parityQueryRow (cached : Bool) (w : Nat → ZMod babyBearModulus) (index : Fin 22) :
    Vector (ZMod babyBearModulus) 8 :=
  (columnParityQueryEntry cached index).map (Expression.eval (Verification.environment w))

/-- The actual active parity controller binds its original transition and selected iota round. -/
theorem parity_native_controller_schedule (cached : Bool) (w : Nat → ZMod babyBearModulus)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (if cached then ColumnParityCached.clockConstraints columnParityFixedTable
        else ColumnParity.clockConstraints columnParityFixedTable)) (active : w 0 = 1) :
    ∃ index : Fin 361, kindAt index.val = .columnParity ∧
      (parityQueryRow cached w 1)[0] = (controlAt index.val : ZMod babyBearModulus) ∧
      (parityQueryRow cached w 1)[2] = (bump (controlAt index.val) : ZMod babyBearModulus) ∧
      (parityQueryRow cached w 1)[3] =
        ((if index.val % 5 = 0 then index.val / 15 else 0 : Nat) : ZMod babyBearModulus) := by
  have sound := column_parity_native_query cached w holds 1
  have tag : (parityQueryRow cached w 1)[7] = 63 := by
    have selected : columnParityQueryTag (1 : Fin 22) = 63 := rfl
    simpa only [parityQueryRow, Vector.getElem_map, selected, Nat.cast_ofNat] using
      column_parity_query_tag cached 1 w
  apply Fixed.Proofs.column_parity_controller_table_sound _
    ((Fixed.Proofs.column_parity_generic_bindings _ sound).2.2.1 tag)
  cases cached <;>
    dsimp only [columnParityQueryEntry, columnParityQuery,
      ColumnParity.importedConstraints, ColumnParityCached.importedConstraints,
      FlatOperation.lookups, List.get, Expression.eval, Verification.environment] <;>
    simp [Expression.eval]
  all_goals
    change (@Vector.mk _ 8 _ _)[1] = 1
    simpa only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
      List.getElem_cons_succ] using active

/-- The native slot key includes the actual execute flag and full control word. -/
theorem parity_native_slot_key (cached : Bool) (w : Nat → ZMod babyBearModulus) :
    (parityQueryRow cached w 0)[0] = (parityQueryRow cached w 1)[0] + 2048 * w 0 := by
  cases cached <;>
    dsimp only [parityQueryRow, columnParityQueryEntry, columnParityQuery,
      ColumnParity.importedConstraints, ColumnParityCached.importedConstraints,
      FlatOperation.lookups, List.get, Expression.eval, Verification.environment] <;>
    norm_num [Fin.getElem_fin, Expression.eval, Verification.environment] <;> ring

/-- Both actual native controller queries bind all six original physical slots. -/
theorem parity_native_slots (cached : Bool) (w : Nat → ZMod babyBearModulus)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (if cached then ColumnParityCached.clockConstraints columnParityFixedTable
        else ColumnParity.clockConstraints columnParityFixedTable)) (active : w 0 = 1)
    (index : Fin 361)
    (control : (parityQueryRow cached w 1)[0] = (controlAt index.val : ZMod babyBearModulus)) :
    ∀ lane : Fin 6, (parityQueryRow cached w 0)[1 + lane.val] =
      ((Call.slots index)[lane.val].val : ZMod babyBearModulus) := by
  have sound := column_parity_native_query cached w holds 0
  have tag : (parityQueryRow cached w 0)[7] = 62 := by
    have selected : columnParityQueryTag (0 : Fin 22) = 62 := rfl
    simpa only [parityQueryRow, Vector.getElem_map, selected, Nat.cast_ofNat] using
      column_parity_query_tag cached 0 w
  apply Fixed.Proofs.column_parity_slot_table_sound _
    ((Fixed.Proofs.column_parity_generic_bindings _ sound).2.1 tag) index
  change (parityQueryRow cached w 0)[0] = ((controlAt index.val + 2048 : Nat) : ZMod babyBearModulus)
  rw [parity_native_slot_key, control, active, Nat.cast_add, Nat.cast_ofNat]
  ring

end Airbender.Keccak.Split.Native.Proofs
