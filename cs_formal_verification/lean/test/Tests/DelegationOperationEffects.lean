import Tests.DelegationCaller
import Tests.BigintMemory
import Slop.Trace.ImageFrame

namespace Tests.DelegationOperationEffects
open Airbender Delegation Trace Arithmetic Reference.RiscV.Sail Reference.Sail
set_option warningAsError true
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

private def assignment (i : Nat) : ZMod babyBearModulus :=
  if i = 1 then 5 else Tests.BigintMemory.row i
private def worker : Delegation.Row babyBearModulus := ⟨.bigint, assignment⟩
private def workers : MemoryData babyBearModulus where
  setup := modeledSetup Keccak.Controller.rows
  rows := [worker]
  initial := worker.memorySteps.map Prod.fst
  terminal := worker.memorySteps.map Prod.snd
private def caller : Trace.Row babyBearModulus PooledFamily :=
  ⟨.addSub, Tests.DelegationCaller.assignment .bigint⟩
private def machine : PooledTrace babyBearModulus where
  rows := [caller]
  rom := ⟨{ name := "unused", Contains _ _ := False }, { name := "unused", Contains _ _ := False }⟩
  initial := caller.start
  terminal := caller.finish
  initialMemory := []
  terminalMemory := []
private def data : Caller.RequestTrace babyBearModulus :=
  ⟨machine, workers, [Tests.DelegationCaller.entry .bigint]⟩
def before : State :=
  wordWriteState Tests.BigintMemory.before 0 (Tests.DelegationCaller.entry .bigint).bits

private theorem worker_constraints : FlatOperation.ConstraintsHoldFlat
    (Verification.environment assignment) (worker.constraints workers.setup) := by
  apply Verification.holds_append
  · simpa [workers, modeledSetup, Bigint.importedConstraints, FlatOperation.ConstraintsHoldFlat,
      Verification.environment, Expression.eval, Lookup.Contains, Table.toRaw, fromElements,
      Verification.range16, assignment, Tests.BigintMemory.row] using Tests.BigintMemory.core
  · simp [Bigint.importedConstraintsTimestampLookups, FlatOperation.ConstraintsHoldFlat]
    repeat' apply And.intro
    all_goals apply Trace.Proofs.range_contains
    all_goals simp [Expression.eval, Verification.environment, assignment, Tests.BigintMemory.row]
    all_goals decide

private theorem accepted : Caller.RequestAccepted data := by
  refine ⟨?_, List.perm_append_comm⟩
  constructor
  · intro row member
    have same : row = caller := List.mem_singleton.mp member
    subst row
    exact Tests.DelegationCaller.satisfies .bigint
  · intro row member
    have same : row = caller := List.mem_singleton.mp member
    subst row
    decide +kernel
  · exact List.Perm.swap _ _ []
  · intro row member
    have same : row = caller := List.mem_singleton.mp member
    subst row
    change ∃ i : Fin 1, Caller.nativeQuery caller.assignment =
      Caller.query ([Tests.DelegationCaller.entry .bigint].get i)
    exact ⟨0, Tests.DelegationCaller.query_bound .bigint⟩
  · exact fun _ present => (List.mem_singleton.mp present).symm ▸ worker_constraints
  · intro row present
    have same : row = worker := List.mem_singleton.mp present
    subst row
    decide +kernel
  · have matching : data.calls = data.fulfillments := by decide +kernel
    rw [← matching]
    exact List.perm_append_comm

private theorem initialized : initialImage before Tests.BigintMemory.cells = some workers.initial := by
  apply Trace.Proofs.image_frame Tests.BigintMemory.initialized
  intro cell member value read
  cases cell with
  | register index => exact rX_register_frame (before := Tests.BigintMemory.before) (after := before) rfl index read
  | ram address =>
    have lower : 4 ≤ address.toNat := by
      simp [Tests.BigintMemory.cells] at member
      rcases member with ⟨i, bound, rfl⟩ | ⟨i, bound, rfl⟩
      all_goals interval_cases i <;> decide
    exact written_word_disjoint 0 _ (Or.inr lower) read

private theorem inputs : Caller.RequestOperationInputs data before [0] Tests.BigintMemory.cells := by
  constructor
  · constructor
    · constructor
      · have bytes : (Cell.ram 0).read before = .ok (Tests.DelegationCaller.entry .bigint).bits before :=
          written_word_read Tests.BigintMemory.before 0 _
        have decoded : run (SailRV32.Functions.encdec_backwards (Tests.DelegationCaller.entry .bigint).bits) before =
            .ok (Tests.DelegationCaller.entry .bigint).instruction before :=
          Tests.DelegationCaller.original_decoder .bigint before
        have fields : Caller.decoderFields (Tests.DelegationCaller.entry .bigint).instruction =
            some (Tests.DelegationCaller.entry .bigint).data := Tests.DelegationCaller.metadata .bigint
        simp only [List.mapM_cons, List.mapM_nil, programEntryRunWith, bytes, decoded, fields,
          bind, Option.bind, pure]
        rfl
      · change 4 < timestampBase ∧ 0 < timestampBase
        norm_num [timestampBase]
      · decide +kernel
    · exact initialized
    · exact Tests.BigintMemory.inputs.publicState.distinct
    · intro cell member
      simp [Tests.BigintMemory.cells] at member
      rcases member with rfl | ⟨i, bound, rfl⟩ | rfl | ⟨i, bound, rfl⟩ | rfl
      all_goals first | trivial | (unfold Cell.Aligned; interval_cases i <;> decide)
  · rfl
  · intro row present family
    have same : row = worker := List.mem_singleton.mp present
    subst row
    cases family

theorem actual_copy_request : Caller.RequestOperationEffects data before Tests.BigintMemory.cells :=
  Caller.operation_soundness accepted inputs

theorem matched_copy_effects :
    ∃ actual ∈ data.workers.rows,
      Requests.fulfillment actual = Requests.caller caller.assignment ∧
      Bigint.Native.ArithmeticEffects actual.assignment := by
  have effects := actual_copy_request.operations worker (by simp [data, workers])
  exact ⟨worker, by simp [data, workers], by decide +kernel, effects⟩

theorem selected_copy_reference :
    Bigint.Additive.spec (Bigint.Native.additiveInput .copy assignment) (Bigint.Native.output assignment) :=
  (actual_copy_request.operations worker (by simp [data, workers])).1 .copy (by decide +kernel)

private def sharedAssignment (i : Nat) : ZMod babyBearModulus :=
  if i = 35 then 4 else Tests.DelegationCaller.assignment .bigint i
private def sharedCaller : Trace.Row babyBearModulus PooledFamily := ⟨.addSub, sharedAssignment⟩
def sharedCells : List Cell := .register 0 :: Tests.BigintMemory.cells
private def sharedMachine : PooledTrace babyBearModulus where
  rows := [sharedCaller]
  rom := machine.rom
  initial := sharedCaller.start
  terminal := sharedCaller.finish
  initialMemory := (Cell.register 0).initialToken 0 :: workers.initial
  terminalMemory := Caller.destinationToken sharedAssignment :: workers.terminal
def sharedData : Caller.RequestTrace babyBearModulus :=
  ⟨sharedMachine, workers, data.program⟩

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

theorem sharedAccepted : Caller.SharedMemoryAccepted sharedData := by
  refine ⟨?_, rfl, ?_⟩
  · constructor
    · intro row member
      have same : row = sharedCaller := List.mem_singleton.mp member
      subst row
      exact sharedCallerConstraints
    · intro row member
      have same : row = sharedCaller := List.mem_singleton.mp member
      subst row
      decide +kernel
    · exact List.Perm.swap _ _ []
    · intro row member
      have same : row = sharedCaller := List.mem_singleton.mp member
      subst row
      change ∃ i : Fin 1, Caller.nativeQuery sharedAssignment = Caller.query ([Tests.DelegationCaller.entry .bigint].get i)
      exact ⟨0, by decide +kernel⟩
    · exact accepted.workerConstraints
    · exact accepted.workerActive
    · exact accepted.requests
  · decide +kernel

theorem sharedInputs : Caller.SharedOperationInputs sharedData before [0] sharedCells := by
  refine ⟨?_, inputs.tables, inputs.rounds⟩
  constructor
  · exact ⟨inputs.publicState.publicProgram.image, inputs.publicState.publicProgram.initialClock,
      inputs.publicState.publicProgram.initialAligned⟩
  · change List.mapM _ (.register 0 :: Tests.BigintMemory.cells) = _
    rw [List.mapM_cons]
    change Option.bind (some ((Cell.register 0).initialToken (p := babyBearModulus) 0))
      (fun token => Option.bind (initialImage before Tests.BigintMemory.cells)
        (fun rest => some (token :: rest))) = _
    rw [initialized]
    rfl
  · decide +kernel
  · intro cell member
    rcases List.mem_cons.mp member with rfl | member
    · trivial
    · exact inputs.publicState.aligned cell member

theorem actual_shared_copy_request : Caller.SharedOperationEffects sharedData before sharedCells :=
  Caller.shared_operation_soundness sharedAccepted sharedInputs

theorem projected_shared_copy_memory :
    MemoryAccepted sharedData.workerProjection ∧
    MemoryInputs sharedData.workerProjection before (Caller.workerCells sharedCells) :=
  ⟨Caller.Proofs.worker_projection_accepted sharedAccepted actual_shared_copy_request.memory.requests,
    Caller.Proofs.worker_projection_inputs sharedInputs.toSharedMemoryInputs actual_shared_copy_request.memory.requests⟩

private def wrongWorkerBoundaries : MemoryData babyBearModulus :=
  { workers with initial := [], terminal := [] }
private def wrongBoundaryData : Caller.RequestTrace babyBearModulus :=
  { sharedData with workers := wrongWorkerBoundaries }

theorem separate_empty_boundaries_rejected : ¬MemoryAccepted wrongWorkerBoundaries := by
  intro valid
  have impossible : ¬(wrongWorkerBoundaries.initial ++ wrongWorkerBoundaries.steps.map Prod.snd).Perm
      (wrongWorkerBoundaries.terminal ++ wrongWorkerBoundaries.steps.map Prod.fst) := by decide +kernel
  exact impossible valid.matching

theorem shared_projection_ignores_private_boundaries :
    wrongBoundaryData.workerProjection = sharedData.workerProjection := rfl

theorem shared_projection_accepts_actual_boundaries : MemoryAccepted wrongBoundaryData.workerProjection := by
  rw [shared_projection_ignores_private_boundaries]
  exact projected_shared_copy_memory.1

end Tests.DelegationOperationEffects
