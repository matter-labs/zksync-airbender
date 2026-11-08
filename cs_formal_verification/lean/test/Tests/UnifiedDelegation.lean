import Tests.DelegationCaller
import Tests.BigintMemory
import Tests.DelegationOperationEffects
import Slop.UnifiedReduced.Claims
import Slop.UnifiedReduced.Completeness.Control
import Slop.UnifiedReduced.Completeness.Binary
import Slop.UnifiedReduced.Completeness.Arith
import Slop.UnifiedReduced.Completeness.Memory
import Slop.UnifiedReduced.Completeness.Call
import Human.Circuits.UnifiedReduced.Tables.Setup

namespace Tests.UnifiedDelegation
open Airbender Trace Arithmetic
set_option warningAsError true
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

/-- The delegation-call row at PC 0, clock 4, issuing CSR `address`. -/
private def callerFrame : UnifiedReduced.Completeness.Frame := ⟨0, 0, 4, 0, 0, 0, 0, 0, 0, 0⟩
private theorem callerFrame_clock : callerFrame.Clock := ⟨by decide, by decide, by decide⟩
private def callWitness (address : ZMod babyBearModulus) : UnifiedReduced.Completeness.Call :=
  ⟨callerFrame, 0, 0, address, 0, 0, 0, 0⟩
private def assignmentWith (address : ZMod babyBearModulus) : Nat → ZMod babyBearModulus :=
  (callWitness address).honest

private def assignment (family : Delegation.Family) := assignmentWith (Delegation.Requests.csr family)

private theorem timestamps (family : Delegation.Family) : FlatOperation.ConstraintsHoldFlat
    (Verification.environment (assignment family)) UnifiedReduced.importedConstraintsTimestampLookups := by
  rw [FlatOperation.constraintsHoldFlat_iff_forall_mem]
  constructor
  · simp [UnifiedReduced.importedConstraintsTimestampLookups, FlatOperation.constraints]
  · rw [List.forall_mem_iff_forall_getElem]
    intro i bound
    have short : i < 8 := by simpa only [UnifiedReduced.timestamp_count] using bound
    interval_cases i
    all_goals apply Trace.Proofs.range_contains
    all_goals cases family <;> decide +kernel

theorem caller_request_retains_full_csr (family : Delegation.Family) :
    (UnifiedReduced.Caller.request (assignment family)).csr = Delegation.Requests.csr family ∧
    31 < (UnifiedReduced.Caller.request (assignment family)).csr := by
  cases family <;> decide +kernel

private def sharedAssignment (column : Nat) : ZMod babyBearModulus :=
  if column = 46 then 4 else assignment .bigint column
private def callFrame : UnifiedReduced.Completeness.Frame := ⟨4, 0, 8, 0, 7, 0, 6, 0, 8, 0⟩
private def arithmeticWitness (value : Nat) : UnifiedReduced.Completeness.Arith :=
  ⟨callFrame, 0, 12, 0, 12, value, 0, 0, 0, 1, 0, value, 0⟩
private def arithmetic (value : Nat) : Nat → ZMod babyBearModulus := (arithmeticWitness value).honest
private theorem sharedTimestamps : FlatOperation.ConstraintsHoldFlat
    (Verification.environment sharedAssignment) UnifiedReduced.importedConstraintsTimestampLookups := by
  rw [FlatOperation.constraintsHoldFlat_iff_forall_mem]
  constructor
  · simp [UnifiedReduced.importedConstraintsTimestampLookups, FlatOperation.constraints]
  · rw [List.forall_mem_iff_forall_getElem]
    intro i bound
    have short : i < 8 := by simpa only [UnifiedReduced.timestamp_count] using bound
    interval_cases i
    all_goals apply Trace.Proofs.range_contains
    all_goals decide +kernel

private theorem arithmeticTimestamps (value : Fin 2) : FlatOperation.ConstraintsHoldFlat
    (Verification.environment (arithmetic value.val)) UnifiedReduced.importedConstraintsTimestampLookups := by
  rw [FlatOperation.constraintsHoldFlat_iff_forall_mem]
  constructor
  · simp [UnifiedReduced.importedConstraintsTimestampLookups, FlatOperation.constraints]
  · rw [List.forall_mem_iff_forall_getElem]
    intro i bound
    have short : i < 8 := by simpa only [UnifiedReduced.timestamp_count] using bound
    interval_cases i
    all_goals apply Trace.Proofs.range_contains
    all_goals fin_cases value <;> decide +kernel

private theorem endpoint_permutation {start finish target : List (MemoryToken babyBearModulus)}
    {steps : List (MemoryToken babyBearModulus × MemoryToken babyBearModulus)}
    (matching : (start ++ steps.map Prod.snd).Perm (finish ++ steps.map Prod.fst))
    (expected : (start ++ steps.map Prod.snd).Perm (target ++ steps.map Prod.fst)) : finish.Perm target :=
  (List.perm_append_right_iff _).mp (matching.symm.trans expected)

private def customWitness : UnifiedReduced.Completeness.Arith :=
  ⟨⟨4, 0, 8, 0, 6, 0, 8, 0, 7, 0⟩, 3, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0⟩
private def rotateWitness (kind : Fin 5) : UnifiedReduced.Completeness.Binary :=
  ⟨⟨4, 0, 8, 0, 6, 0, 7, 0, 9, 0⟩, 0, true, kind.val - 1, false, 0, 12, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩
private def customAssignment (kind : Fin 5) : Nat → ZMod babyBearModulus :=
  if kind.val = 0 then customWitness.honest else (rotateWitness kind).honest
private theorem customClocks (kind : Fin 5) : FlatOperation.ConstraintsHoldFlat
    (Verification.environment (customAssignment kind)) UnifiedReduced.importedConstraintsTimestampLookups := by
  rw [FlatOperation.constraintsHoldFlat_iff_forall_mem]
  constructor
  · simp [UnifiedReduced.importedConstraintsTimestampLookups, FlatOperation.constraints]
  · rw [List.forall_mem_iff_forall_getElem]
    intro i bound
    have short : i < 8 := by simpa only [UnifiedReduced.timestamp_count] using bound
    interval_cases i
    all_goals apply Trace.Proofs.range_contains
    all_goals fin_cases kind <;> decide +kernel

private def binaryWitness : UnifiedReduced.Completeness.Binary :=
  ⟨callFrame, 4, false, 0, true, 12, 0, 12, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩
private def binaryAssignment : Nat → ZMod babyBearModulus := binaryWitness.honest
private theorem binaryClocks : FlatOperation.ConstraintsHoldFlat
    (Verification.environment binaryAssignment) UnifiedReduced.importedConstraintsTimestampLookups := by
  rw [FlatOperation.constraintsHoldFlat_iff_forall_mem]
  constructor
  · simp [UnifiedReduced.importedConstraintsTimestampLookups, FlatOperation.constraints]
  · rw [List.forall_mem_iff_forall_getElem]
    intro i bound
    have short : i < 8 := by simpa only [UnifiedReduced.timestamp_count] using bound
    interval_cases i
    all_goals apply Trace.Proofs.range_contains
    all_goals decide +kernel

private def comparisonWitness : UnifiedReduced.Completeness.Control :=
  ⟨callFrame, 2, false, 3, 12, 0, 12, 0, 0, 0, 0, 65535, 65535, 0, 0⟩
private def comparisonAssignment : Nat → ZMod babyBearModulus := comparisonWitness.honest
private theorem comparisonClocks : FlatOperation.ConstraintsHoldFlat
    (Verification.environment comparisonAssignment) UnifiedReduced.importedConstraintsTimestampLookups := by
  rw [FlatOperation.constraintsHoldFlat_iff_forall_mem]
  constructor
  · simp [UnifiedReduced.importedConstraintsTimestampLookups, FlatOperation.constraints]
  · rw [List.forall_mem_iff_forall_getElem]
    intro i bound
    have short : i < 8 := by simpa only [UnifiedReduced.timestamp_count] using bound
    interval_cases i
    all_goals apply Trace.Proofs.range_contains
    all_goals decide +kernel

private def controlWitness (kind : Fin 4) : UnifiedReduced.Completeness.Control :=
  ⟨⟨4, 0, 8, 0, if kind.val = 2 then 6 else 7, 0, if kind.val = 2 then 8 else 6, 0,
      if kind.val < 2 then 9 else if kind.val = 2 then 7 else 8, 0⟩,
    if kind.val < 2 then 3 else kind.val - 2, decide (kind.val < 2), if kind.val = 1 then 1 else 0,
    if kind.val = 2 then 0 else 12, 0, if kind.val < 2 then 0 else 12, 0, 0, 0, 0,
    if kind.val = 3 then 12 else 8, 0, 0, 0⟩
private def controlAssignment (kind : Fin 4) : Nat → ZMod babyBearModulus := (controlWitness kind).honest
private theorem controlClocks (kind : Fin 4) : FlatOperation.ConstraintsHoldFlat
    (Verification.environment (controlAssignment kind)) UnifiedReduced.importedConstraintsTimestampLookups := by
  rw [FlatOperation.constraintsHoldFlat_iff_forall_mem]
  constructor
  · simp [UnifiedReduced.importedConstraintsTimestampLookups, FlatOperation.constraints]
  · rw [List.forall_mem_iff_forall_getElem]
    intro i bound
    have short : i < 8 := by simpa only [UnifiedReduced.timestamp_count] using bound
    interval_cases i
    all_goals apply Trace.Proofs.range_contains
    all_goals fin_cases kind <;> decide +kernel

/-- LW x12, 0(x10) / SW x12, 0(x10) at PC 4 with x10 = 0x400000 and the word 0. -/
private def memoryWitness (store : Bool) : UnifiedReduced.Completeness.Memory :=
  ⟨⟨4, 0, 8, 0, 7, 0, 7, 0, 7, 0⟩, store, 10, 12, 0, 64, 0, 0, 0, 0, 0, 0⟩
private def memoryAssignment (store : Bool) : Nat → ZMod babyBearModulus := (memoryWitness store).honest
private theorem memoryClocks (store : Bool) : FlatOperation.ConstraintsHoldFlat
    (Verification.environment (memoryAssignment store)) UnifiedReduced.importedConstraintsTimestampLookups := by
  rw [FlatOperation.constraintsHoldFlat_iff_forall_mem]
  constructor
  · simp [UnifiedReduced.importedConstraintsTimestampLookups, FlatOperation.constraints]
  · rw [List.forall_mem_iff_forall_getElem]
    intro i bound
    have short : i < 8 := by simpa only [UnifiedReduced.timestamp_count] using bound
    interval_cases i
    all_goals apply Trace.Proofs.range_contains
    all_goals cases store <;> decide +kernel

private def abiAssignment (highControl : Bool) (column : Nat) : ZMod babyBearModulus :=
  if column = 55 ∨ column = 56 ∨ column = 59 then (if highControl then 1 else 0)
  else if column = 66 then 0
  else if column = 1 then 5 else Tests.BigintMemory.row column
private theorem abiCore (highControl : Bool) : FlatOperation.ConstraintsHoldFlat
    (Verification.environment (abiAssignment highControl))
    (Bigint.importedConstraints Bigint.setupTable) := by
  cases highControl <;> simp [Bigint.importedConstraints, FlatOperation.ConstraintsHoldFlat,
    Verification.environment, Expression.eval, abiAssignment, Tests.BigintMemory.row,
    Lookup.Contains, Table.toRaw, fromElements]
  repeat' apply And.intro
  all_goals solve
    | decide +kernel
    | (apply Verification.range16_contains; decide +kernel)
    | (apply Trace.Proofs.range_contains; decide +kernel)
    | (refine ⟨⟨0, by decide +kernel⟩, ?_⟩; decide +kernel)
    | (refine ⟨⟨262144, by decide +kernel⟩, ?_⟩; decide +kernel)
    | (refine ⟨⟨1310720, by decide +kernel⟩, ?_⟩; decide +kernel)
    | (refine ⟨⟨1312768, by decide +kernel⟩, ?_⟩; decide +kernel)
    | (refine ⟨⟨1316864, by decide +kernel⟩, ?_⟩; decide +kernel)
    | (refine ⟨⟨1325056, by decide +kernel⟩, ?_⟩; decide +kernel)

private theorem abiTimestamps (highControl : Bool) : FlatOperation.ConstraintsHoldFlat
    (Verification.environment (abiAssignment highControl)) Bigint.importedConstraintsTimestampLookups := by
  simp [Bigint.importedConstraintsTimestampLookups, FlatOperation.ConstraintsHoldFlat]
  repeat' apply And.intro
  all_goals apply Trace.Proofs.range_contains
  all_goals simp [Expression.eval, Verification.environment, abiAssignment, Tests.BigintMemory.row]
  all_goals decide +kernel

end Tests.UnifiedDelegation
