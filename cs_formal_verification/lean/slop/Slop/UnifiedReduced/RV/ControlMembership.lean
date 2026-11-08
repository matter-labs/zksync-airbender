module
public import Slop.UnifiedReduced.ControlProjection
public import Slop.UnifiedReduced.RV.ControlResolution
public import Slop.JumpBranchSlt.ArtifactChecks
public import Slop.JumpBranchSlt.OpIndex
public import Mathlib.Tactic.IntervalCases
import all Init.Data.Array.Basic -- until Lean 4.35 exposes Array/Vector ofFn/DecidableEq (lean4#14989, #14988, #14270)

@[expose] public section

namespace Airbender.UnifiedReduced.Proofs.RV
open Arithmetic Verification
set_option warningAsError true
set_option maxRecDepth 16384

theorem control_constraints [Fact p.Prime] (hp : 4194304 ≤ p)
    {words : Nat → BitVec 32} {w : Nat → ZMod p}
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints (Setup.tableWith words)))
    (jumps : w 21 = 0 ∧ w 22 = 0) (selected : w 23 + w 24 = 1)
    (discarded : w 24 * (1 - w 25) = 0)
    (binary : w 26 = 0 ∧ w 27 = 0) (rom : w 81 = 0)
    (leftHi : (w 37).val < 65536) (rightHi : (w 60).val < 65536)
    (funct : (w 10).val < 8) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment (controlAssignment w))
      JumpBranchSlt.importedConstraints := by
  have total : w 21 + w 22 + w 23 + w 24 = 1 := by simp [jumps.1, jumps.2, selected]
  have values := control_lookup_values hp holds total binary rom
  have query (i : Fin 13) := Verification.lookup_of_holds holds
    ⟨i.val, by rw [lookup_count]; have := i.isLt; omega⟩
  have q0 := query 0; have q1 := query 1; have q4 := query 4; have q5 := query 5
  op_index at q0 q1 q4 q5
  have a := range16_bound q0; have b := range16_bound q1
  have raw := range16_bound q5
  simp [Expression.eval, Verification.environment] at a b raw
  have zeroBound : (w 74 + w 75).val < 131072 := by
    rw [ZMod.val_add]
    have mod := Nat.mod_le ((w 74).val + (w 75).val) p
    dsimp [limbBase] at a b
    omega
  have zero : (pairLookup regIsZeroTable (.var ⟨74⟩ + .var ⟨75⟩) (.var ⟨57⟩)).Contains
      (Verification.environment w) := by
    apply (pairLookup regIsZeroTable _ _).table.implied_by_completeness
    apply (Lookup.completeness_def regIsZeroTable (Verification.environment w)
      (.var ⟨74⟩ + .var ⟨75⟩, .var ⟨57⟩)).mpr
    with_unfolding_all change ∃ i : Fin 131072, (w 74 + w 75, w 57) =
      ((i.val : ZMod p), ((if i.val = 0 then 1 else 0 : Nat) : ZMod p))
    refine ⟨⟨(w 74 + w 75).val, zeroBound⟩, ?_⟩
    exact Prod.ext (ZMod.natCast_zmod_val _).symm (by simpa using values.1)
  have sign : (pairLookup u16SignTable (.var ⟨37⟩) (.var ⟨58⟩)).Contains
      (Verification.environment w) := by
    apply (pairLookup u16SignTable _ _).table.implied_by_completeness
    apply (Lookup.completeness_def u16SignTable (Verification.environment w) (.var ⟨37⟩, .var ⟨58⟩)).mpr
    with_unfolding_all change ∃ i : Fin 65536, (w 37, w 58) =
      ((i.val : ZMod p), ((i.val / 32768 : Nat) : ZMod p))
    exact ⟨⟨(w 37).val, leftHi⟩, Prod.ext (ZMod.natCast_zmod_val _).symm values.2.1⟩
  have cleanup : (jumpCleanup (.var ⟨64⟩) (.var ⟨56⟩) (.var ⟨30⟩)).Contains
      (Verification.environment w) := by
    apply (jumpCleanup _ _ _).table.implied_by_completeness
    apply (Lookup.completeness_def jumpCleanupTable (Verification.environment w)
      (.var ⟨64⟩, .var ⟨56⟩, .var ⟨30⟩)).mpr
    with_unfolding_all change ∃ i : Fin 65536, (w 64, w 56, w 30) =
      ((i.val : ZMod p), ((i.val / 2 % 2 : Nat) : ZMod p), ((i.val - i.val % 4 : Nat) : ZMod p))
    exact ⟨⟨(w 64).val, raw⟩, Prod.ext (ZMod.natCast_zmod_val _).symm
      (Prod.ext values.2.2.2.2.2.1 values.2.2.2.2.2.2)⟩
  have condition := control_conditional_lookup hp holds total binary rom leftHi rightHi funct
  apply FlatOperation.constraintsHoldFlat_iff_forall_mem.mpr
  constructor
  · intro expression member
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp member
    exact control_assertions holds jumps selected discarded ⟨i.val, by simpa only [JumpBranchSlt.constraint_count] using i.isLt⟩
  · intro lookup member
    obtain ⟨⟨k, hk⟩, rfl⟩ := List.mem_iff_get.mp member
    have bound : k < 8 := by simpa only [JumpBranchSlt.lookup_count] using hk
    interval_cases k
    all_goals op_index
    -- The imported lookups in order: four ranges, zero test, sign, conditional and cleanup.
    · simpa [Lookup.Contains, controlAssignment, range16, pairLookup, jumpCleanup, Vector.map, Expression.eval,
        Verification.environment] using q0
    · simpa [Lookup.Contains, controlAssignment, range16, pairLookup, jumpCleanup, Vector.map, Expression.eval,
        Verification.environment] using q1
    · simpa [Lookup.Contains, controlAssignment, range16, pairLookup, jumpCleanup, Vector.map, Expression.eval,
        Verification.environment] using q4
    · simpa [Lookup.Contains, controlAssignment, range16, pairLookup, jumpCleanup, Vector.map, Expression.eval,
        Verification.environment] using q5
    · simpa [Lookup.Contains, controlAssignment, range16, pairLookup, jumpCleanup, Vector.map, Expression.eval,
        Verification.environment] using zero
    · simpa [Lookup.Contains, controlAssignment, range16, pairLookup, jumpCleanup, Vector.map, Expression.eval,
        Verification.environment] using sign
    · simpa [Lookup.Contains, controlAssignment, range16, pairLookup, jumpCleanup, Vector.map, Expression.eval,
        Verification.environment, add_assoc, add_comm, add_left_comm] using condition
    · simpa [Lookup.Contains, controlAssignment, range16, pairLookup, jumpCleanup, Vector.map, Expression.eval,
        Verification.environment] using cleanup

end Airbender.UnifiedReduced.Proofs.RV
