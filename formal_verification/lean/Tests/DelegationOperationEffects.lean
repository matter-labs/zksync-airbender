import Tests.DelegationCaller
import Tests.BigintMemory
import Airbender.Proofs.Trace.ImageFrame

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
private def before : State :=
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

end Tests.DelegationOperationEffects
