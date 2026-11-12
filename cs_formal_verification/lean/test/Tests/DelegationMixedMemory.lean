module
public import Tests.DelegationOperationEffects
public import Slop.Delegation.RequestWindows
public import Slop.Delegation.SharedOperations
public import Slop.Delegation.WorkerProjection
public import Slop.JumpBranchSlt.Branch
public import Slop.JumpBranchSlt.Jump
public import Slop.MulDiv.Values
public import Slop.SubwordMemory.Values
public import Slop.CleanCore.Circuit.Operations

@[expose] public section

namespace Tests.DelegationMixedMemory
open Airbender Delegation Trace Arithmetic
set_option warningAsError true
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000

def arithmetic (value : Nat) : Nat → ZMod babyBearModulus
  | 0 => 4
  | 2 | 19 | 35 => 8
  | 21 | 5 | 7 => 12
  | 4 | 8 | 10 | 42 | 43 | 44 => 1
  | 23 => 7
  | 27 => 6
  | 25 => value
  | 33 => value + 1
  | _ => 0
private theorem local_constraints (value : Fin 2) : FlatOperation.ConstraintsHoldFlat
    (Verification.environment (arithmetic value.val)) AddSub.clockConstraints := by
  apply Verification.holds_append
  · rw [FlatOperation.constraintsHoldFlat_iff_forall_mem]
    constructor
    · fin_cases value <;> decide +kernel
    · rw [List.forall_mem_iff_forall_getElem]
      intro i bound
      have short : i < 6 := by simpa only [AddSub.lookup_count] using bound
      interval_cases i
      all_goals apply Verification.range16_contains
      all_goals fin_cases value <;> decide +kernel
  · rw [FlatOperation.constraintsHoldFlat_iff_forall_mem]
    constructor
    · simp [AddSub.importedConstraintsTimestampLookups, FlatOperation.constraints]
    · rw [List.forall_mem_iff_forall_getElem]
      intro i bound
      have short : i < 8 := by simpa only [AddSub.timestamp_count] using bound
      interval_cases i
      all_goals apply Trace.Proofs.range_contains
      all_goals fin_cases value <;> decide +kernel

theorem fabricated_read_locally_satisfies : FlatOperation.ConstraintsHoldFlat
    (Verification.environment (arithmetic 1)) AddSub.clockConstraints := local_constraints 1

end Tests.DelegationMixedMemory
