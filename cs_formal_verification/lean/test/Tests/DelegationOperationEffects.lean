module
public import Tests.DelegationCaller
public import Tests.BigintMemory
public import Slop.KernelRfl
public import Slop.Trace.InitialImage
public import Slop.CleanCore.Circuit.Operations

@[expose] public section

namespace Tests.DelegationOperationEffects
noncomputable section
open Airbender Delegation Trace Arithmetic
set_option warningAsError true
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

-- `NonVacuous.Bigint.row` already carries the active invocation clock 5.
def assignment (i : Nat) : ZMod babyBearModulus := NonVacuous.Bigint.row i
def worker : Delegation.Row babyBearModulus := ⟨.bigint, assignment⟩
def workers : MemoryData babyBearModulus where
  setup := modeledSetup Keccak.Controller.rows
  rows := [worker]
  initial := worker.memorySteps.map Prod.fst
  terminal := worker.memorySteps.map Prod.snd
private theorem worker_constraints : FlatOperation.ConstraintsHoldFlat
    (Verification.environment assignment) (worker.constraints workers.setup) := by
  apply Verification.holds_append
  · exact NonVacuous.Bigint.core
  · simp [Bigint.importedConstraintsTimestampLookups, FlatOperation.ConstraintsHoldFlat]
    repeat' apply And.intro
    all_goals apply Trace.Proofs.range_contains
    all_goals simp [Expression.eval, Verification.environment, assignment, NonVacuous.Bigint.row]
    all_goals decide

private def sharedAssignment (i : Nat) : ZMod babyBearModulus :=
  if i = 35 then 4 else Tests.DelegationCaller.assignment .bigint i
def sharedCells : List Cell := .register 0 :: NonVacuous.Bigint.cells
private theorem sharedCallerConstraints : FlatOperation.ConstraintsHoldFlat
    (Verification.environment sharedAssignment) AddSub.clockConstraints := by
  apply Verification.holds_append
  · rw [FlatOperation.constraintsHoldFlat_iff_forall_mem]
    constructor
    · decide +kernel
    · rw [List.forall_mem_iff_forall_getElem]
      intro i bound
      have short : i < 6 := by simpa only [AddSub.lookup_count] using bound
      interval_cases i
      all_goals apply Verification.range16_contains
      all_goals decide +kernel
  · rw [FlatOperation.constraintsHoldFlat_iff_forall_mem]
    constructor
    · simp [AddSub.importedConstraintsTimestampLookups, FlatOperation.constraints]
    · rw [List.forall_mem_iff_forall_getElem]
      intro i bound
      have short : i < 8 := by simpa only [AddSub.timestamp_count] using bound
      interval_cases i
      all_goals apply Trace.Proofs.range_contains
      all_goals decide +kernel

def wrongWorkerBoundaries : MemoryData babyBearModulus :=
  { workers with initial := [], terminal := [] }
theorem separate_empty_boundaries_rejected : ¬MemoryAccepted wrongWorkerBoundaries := by
  intro valid
  have impossible : ¬(wrongWorkerBoundaries.initial ++ wrongWorkerBoundaries.steps.map Prod.snd).Perm
      (wrongWorkerBoundaries.terminal ++ wrongWorkerBoundaries.steps.map Prod.fst) := by decide +kernel
  exact impossible valid.matching

end

end Tests.DelegationOperationEffects
