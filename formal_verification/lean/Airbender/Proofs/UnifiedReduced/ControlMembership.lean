import Airbender.Proofs.UnifiedReduced.ControlProjection

namespace Airbender.UnifiedReduced.Proofs
open Arithmetic Verification
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

theorem control_constraints [Fact p.Prime] (hp : 4194304 ≤ p)
    {before : Reference.RiscV.Sail.State} {w : Nat → ZMod p}
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints (Setup.table before)))
    (jumps : w 21 = 0 ∧ w 22 = 0) (selected : w 23 + w 24 = 1)
    (discarded : w 24 * (1 - w 25) = 0)
    (binary : w 26 = 0 ∧ w 27 = 0) (rom : w 87 = 0)
    (leftHi : (w 37).val < 65536) (rightHi : (w 60).val < 65536)
    (funct : (w 10).val < 8) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment (controlAssignment w))
      JumpBranchSlt.importedConstraints := by
  have total : w 21 + w 22 + w 23 + w 24 = 1 := by simp [jumps.1, jumps.2, selected]
  have values := control_lookup_values hp holds total binary rom
  have query (i : Fin 13) := Verification.lookup_of_holds holds
    ⟨i.val, by rw [lookup_count]; have := i.isLt; omega⟩
  have a := range16_bound (query 0); have b := range16_bound (query 1)
  have raw := range16_bound (query 5)
  simp [Expression.eval, Verification.environment] at a b raw
  have zeroBound : (w 78 + w 79).val < 131072 := by
    rw [ZMod.val_add]
    have mod := Nat.mod_le ((w 78).val + (w 79).val) p
    dsimp [limbBase] at a b
    omega
  have zero : (pairLookup regIsZeroTable (.var ⟨78⟩ + .var ⟨79⟩) (.var ⟨57⟩)).Contains
      (Verification.environment w) := by
    apply (pairLookup regIsZeroTable _ _).table.implied_by_completeness
    apply (Lookup.completeness_def regIsZeroTable (Verification.environment w)
      (.var ⟨78⟩ + .var ⟨79⟩, .var ⟨57⟩)).mpr
    with_unfolding_all change ∃ i : Fin 131072, (w 78 + w 79, w 57) =
      ((i.val : ZMod p), ((if i.val = 0 then 1 else 0 : Nat) : ZMod p))
    refine ⟨⟨(w 78 + w 79).val, zeroBound⟩, ?_⟩
    exact Prod.ext (ZMod.natCast_zmod_val _).symm (by simpa using values.1)
  have sign : (pairLookup u16SignTable (.var ⟨37⟩) (.var ⟨58⟩)).Contains
      (Verification.environment w) := by
    apply (pairLookup u16SignTable _ _).table.implied_by_completeness
    apply (Lookup.completeness_def u16SignTable (Verification.environment w) (.var ⟨37⟩, .var ⟨58⟩)).mpr
    with_unfolding_all change ∃ i : Fin 65536, (w 37, w 58) =
      ((i.val : ZMod p), ((i.val / 32768 : Nat) : ZMod p))
    exact ⟨⟨(w 37).val, leftHi⟩, Prod.ext (ZMod.natCast_zmod_val _).symm values.2.1⟩
  have cleanup : (jumpCleanup (.var ⟨81⟩) (.var ⟨56⟩) (.var ⟨30⟩)).Contains
      (Verification.environment w) := by
    apply (jumpCleanup _ _ _).table.implied_by_completeness
    apply (Lookup.completeness_def jumpCleanupTable (Verification.environment w)
      (.var ⟨81⟩, .var ⟨56⟩, .var ⟨30⟩)).mpr
    with_unfolding_all change ∃ i : Fin 65536, (w 81, w 56, w 30) =
      ((i.val : ZMod p), ((i.val / 2 % 2 : Nat) : ZMod p), ((i.val - i.val % 4 : Nat) : ZMod p))
    exact ⟨⟨(w 81).val, raw⟩, Prod.ext (ZMod.natCast_zmod_val _).symm
      (Prod.ext values.2.2.2.2.2.1 values.2.2.2.2.2.2)⟩
  have condition := control_conditional_lookup hp holds total binary rom leftHi rightHi funct
  apply FlatOperation.constraintsHoldFlat_iff_forall_mem.mpr
  constructor
  · intro expression member
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp member
    exact control_assertions holds jumps selected discarded ⟨i.val, by simpa only [JumpBranchSlt.constraint_count] using i.isLt⟩
  · intro lookup member
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp member
    change Fin 8 at i
    fin_cases i
    all_goals first
      | simpa [JumpBranchSlt.importedConstraints, importedConstraints, FlatOperation.lookups, controlAssignment, range16, pairLookup, jumpCleanup, Vector.map, Lookup.Contains, Expression.eval, Verification.environment] using query 0
      | simpa [JumpBranchSlt.importedConstraints, importedConstraints, FlatOperation.lookups, controlAssignment, range16, pairLookup, jumpCleanup, Vector.map, Lookup.Contains, Expression.eval, Verification.environment] using query 1
      | simpa [JumpBranchSlt.importedConstraints, importedConstraints, FlatOperation.lookups, controlAssignment, range16, pairLookup, jumpCleanup, Vector.map, Lookup.Contains, Expression.eval, Verification.environment] using query 4
      | simpa [JumpBranchSlt.importedConstraints, importedConstraints, FlatOperation.lookups, controlAssignment, range16, pairLookup, jumpCleanup, Vector.map, Lookup.Contains, Expression.eval, Verification.environment] using query 5
      | simpa [JumpBranchSlt.importedConstraints, importedConstraints, FlatOperation.lookups, controlAssignment, range16, pairLookup, jumpCleanup, Vector.map, Lookup.Contains, Expression.eval, Verification.environment] using zero
      | simpa [JumpBranchSlt.importedConstraints, importedConstraints, FlatOperation.lookups, controlAssignment, range16, pairLookup, jumpCleanup, Vector.map, Lookup.Contains, Expression.eval, Verification.environment] using sign
      | simpa [JumpBranchSlt.importedConstraints, importedConstraints, FlatOperation.lookups, controlAssignment, range16, pairLookup, jumpCleanup, Vector.map, Lookup.Contains, Expression.eval, Verification.environment, add_assoc, add_comm, add_left_comm] using condition
      | simpa [JumpBranchSlt.importedConstraints, importedConstraints, FlatOperation.lookups, controlAssignment, range16, pairLookup, jumpCleanup, Vector.map, Lookup.Contains, Expression.eval, Verification.environment] using cleanup

end Airbender.UnifiedReduced.Proofs
