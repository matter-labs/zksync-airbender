import Airbender.Proofs.Keccak.SplitChiControllerRows
import Airbender.Proofs.Keccak.SplitChiNativeLookup

namespace Airbender.Keccak.Split.Native.Proofs
set_option warningAsError true
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
variable [Fact babyBearModulus.Prime]

/-- The first actual native lookup is the chi5 controller query. -/
def chi5ControllerQuery (cached : Bool) : Lookup (ZMod babyBearModulus) :=
  match cached with
  | false => (FlatOperation.lookups (Chi5.importedConstraints chi5FixedTable)).get ⟨0, by change 0 < 17; decide⟩
  | true => (FlatOperation.lookups (Chi5Cached.importedConstraints chi5FixedTable)).get ⟨0, by change 0 < 17; decide⟩

theorem chi5_controller_table (cached : Bool) :
    (chi5ControllerQuery cached).table = chi5FixedTable.toRaw := by
  cases cached <;> rfl

theorem chi5_controller_arity (cached : Bool) : (chi5ControllerQuery cached).table.arity = 11 := by
  rw [chi5_controller_table]
  rfl

/-- Complete evaluated native controller fields, including the constant table tag. -/
def chi5ControllerRow (cached : Bool) (w : Nat → ZMod babyBearModulus) :
    Vector (ZMod babyBearModulus) 11 :=
  ((chi5ControllerQuery cached).entry.cast (chi5_controller_arity cached)).map
    (Expression.eval (Verification.environment w))

theorem chi5_controller_query_shape (cached : Bool) (w : Nat → ZMod babyBearModulus) :
    (chi5ControllerQuery cached).entry.map (Expression.eval (Verification.environment w)) =
      (chi5ControllerRow cached w).cast (chi5_controller_arity cached).symm := by
  cases cached <;> rfl

/-- An active native row uses the exact blessed control transition and physical slots. -/
theorem chi5_native_controller_schedule (cached : Bool) (w : Nat → ZMod babyBearModulus)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (if cached then Chi5Cached.clockConstraints chi5FixedTable else Chi5.clockConstraints chi5FixedTable))
    (active : w 0 = 1) :
    ∃ index : Fin 361, kindAt index.val = .chi5 ∧
      (chi5ControllerRow cached w)[0] = (controlAt index.val : ZMod babyBearModulus) ∧
      (chi5ControllerRow cached w)[2] = (bump (controlAt index.val) : ZMod babyBearModulus) ∧
      (∀ lane : Fin 5, (chi5ControllerRow cached w)[3 + lane.val] =
        ((Call.slots index)[lane.val].val : ZMod babyBearModulus)) ∧
      (chi5ControllerRow cached w)[8] = ((index.val % 5 : Nat) : ZMod babyBearModulus) := by
  have member : (chi5ControllerQuery cached).Contains (Verification.environment w) := by
    cases cached
    · exact Verification.lookup_of_holds (Verification.holds_of_sublist holds
        (List.sublist_append_left _ _)) ⟨0, by change 0 < 17; decide⟩
    · exact Verification.lookup_of_holds (Verification.holds_of_sublist holds
        (List.sublist_append_left _ _)) ⟨0, by change 0 < 17; decide⟩
  have sound : chi5FixedTable.toRaw.Soundness #[] (chi5ControllerRow cached w) := by
    cases cached <;> exact (chi5ControllerQuery _).table.imply_soundness _ _ member
  apply Fixed.Proofs.chi5_generic_controller_schedule _ sound
  · cases cached <;>
      dsimp only [chi5ControllerRow, chi5ControllerQuery, Chi5.importedConstraints,
        Chi5Cached.importedConstraints, FlatOperation.lookups, List.get, Expression.eval,
        Verification.environment] <;>
      norm_num [Fin.getElem_fin, Expression.eval, Verification.environment]
  · cases cached <;>
      dsimp only [chi5ControllerRow, chi5ControllerQuery, Chi5.importedConstraints,
        Chi5Cached.importedConstraints, FlatOperation.lookups, List.get, Expression.eval,
        Verification.environment] <;>
      simpa [Fin.getElem_fin, Expression.eval, Verification.environment] using active

end Airbender.Keccak.Split.Native.Proofs
