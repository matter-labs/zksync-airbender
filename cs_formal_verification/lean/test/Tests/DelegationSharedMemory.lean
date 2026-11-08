import Tests.DelegationCaller
import Tests.DelegationMemory
import Human.Helpers.Delegation.SharedMemory
import Slop.Delegation.RequestTrace
import Slop.Trace.TransferValues

namespace Tests.DelegationSharedMemory
open Airbender Delegation Trace Arithmetic
set_option warningAsError true
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

private def assignment (source : Nat) (i : Nat) : ZMod babyBearModulus :=
  if i = 35 then 4 else if i = 25 then source else Tests.DelegationCaller.assignment .keccak i
private theorem caller_constraints (source : Fin 2) : FlatOperation.ConstraintsHoldFlat
    (Verification.environment (assignment source.val)) AddSub.clockConstraints := by
  apply Verification.holds_append
  · rw [FlatOperation.constraintsHoldFlat_iff_forall_mem]
    constructor
    · fin_cases source <;> decide +kernel
    · rw [List.forall_mem_iff_forall_getElem]
      intro i bound
      have short : i < 6 := by simpa only [AddSub.lookup_count] using bound
      interval_cases i
      all_goals apply Verification.range16_contains
      all_goals fin_cases source <;> decide +kernel
  · rw [FlatOperation.constraintsHoldFlat_iff_forall_mem]
    constructor
    · simp [AddSub.importedConstraintsTimestampLookups, FlatOperation.constraints]
    · rw [List.forall_mem_iff_forall_getElem]
      intro i bound
      have short : i < 8 := by simpa only [AddSub.timestamp_count] using bound
      interval_cases i
      all_goals apply Trace.Proofs.range_contains
      all_goals fin_cases source <;> decide +kernel

theorem changed_source_locally_satisfies : FlatOperation.ConstraintsHoldFlat
    (Verification.environment (assignment 1)) AddSub.clockConstraints :=
  caller_constraints 1

end Tests.DelegationSharedMemory
