module
public import Tests.BigintMemory
public import Tests.DelegationCaller
public import Tests.DelegationOperationEffects
public import Slop.Delegation.RequestTrace
public import Human.Helpers.Memory.Native
public import Slop.Trace.ROMView
import all Init.Data.Array.Basic -- Init.Data.Array.Basic is only partly exposed (still true in 4.35)

@[expose] public section

namespace Tests.DelegationROMBoundary
noncomputable section
open Airbender Delegation Trace Arithmetic
set_option warningAsError true
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

def assignment (column : Nat) : ZMod babyBearModulus :=
  if column = 1 then 5 else if column = 4 ∨ column = 38 then 0 else Tests.BigintMemory.row column
def worker : Delegation.Row babyBearModulus := ⟨.bigint, assignment⟩
def workers : MemoryData babyBearModulus where
  setup := modeledSetup Keccak.Controller.rows
  rows := [worker]
  initial := worker.memorySteps.map Prod.fst
  terminal := worker.memorySteps.map Prod.snd
private theorem core : FlatOperation.ConstraintsHoldFlat (Verification.environment assignment)
    (Bigint.importedConstraints Bigint.setupTable) := by
  simp [Bigint.importedConstraints, FlatOperation.ConstraintsHoldFlat,
    Verification.environment, Expression.eval, assignment, Tests.BigintMemory.row, Lookup.Contains, Table.toRaw, fromElements]
  repeat' apply And.intro
  all_goals solve
    | (apply Verification.range16_contains; decide +kernel)
    | (apply Trace.Proofs.range_contains; decide +kernel)
    | (refine ⟨⟨0, by decide⟩, ?_⟩; decide +kernel)
    | (refine ⟨⟨262144, by decide⟩, ?_⟩; decide +kernel)
    | (refine ⟨⟨1310720, by decide⟩, ?_⟩; decide +kernel)
    | (refine ⟨⟨1312768, by decide⟩, ?_⟩; decide +kernel)
    | (refine ⟨⟨1316864, by decide⟩, ?_⟩; decide +kernel)
    | (refine ⟨⟨1325056, by decide⟩, ?_⟩; decide +kernel)

private theorem clocks : FlatOperation.ConstraintsHoldFlat (Verification.environment assignment)
    Bigint.importedConstraintsTimestampLookups := by
  rw [FlatOperation.constraintsHoldFlat_iff_forall_mem]
  constructor
  · simp [Bigint.importedConstraintsTimestampLookups, FlatOperation.constraints]
  · rw [List.forall_mem_iff_forall_getElem]
    intro i bound
    have short : i < 41 := by simpa only [Bigint.timestamp_count] using bound
    interval_cases i
    all_goals apply Trace.Proofs.range_contains
    all_goals decide +kernel

theorem worker_constraints : FlatOperation.ConstraintsHoldFlat
    (Verification.environment assignment) (worker.constraints workers.setup) :=
  Verification.holds_append core clocks

def statePort : MemoryPort := worker.ports[1]'(by decide +kernel)

theorem supported_copy_mode : assignment 66 = 1 ∧ assignment 55 = 128 ∧ assignment 56 = 0 := by
  decide +kernel

theorem worker_accesses_rom : statePort ∈ worker.ports ∧
    statePort.address.code assignment = (Cell.ram 0).addressCode ∧
    Trace.ROMView.shadow (statePort.address.code assignment) := by
  decide +kernel

end

end Tests.DelegationROMBoundary
