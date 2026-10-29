import Airbender.Proofs.UnifiedReduced.StreamROMPathCallABI
import Airbender.Proofs.UnifiedReduced.StreamNativeCalls

namespace Airbender.UnifiedReduced.Caller.Stream.Proofs
open Trace Trace.Proofs Arithmetic Reference.RiscV.Sail
open Caller.Proofs
set_option warningAsError true
set_option Elab.async false

/-- Actual native worker calls use explicit bigint and hash input contracts. -/
theorem native_worker_call_of_binding
    {data : RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry}
    {initial before after : State} {ca oa : List (BitVec 32)} {cells historyCells : List Cell}
    {events : List MemoryAccess} {worker : Delegation.Row babyBearModulus}
    (accepted : MixedMemoryAccepted data program)
    (inputs : NativeMemoryInputsWith Stream.decoderFields data program initial ca oa cells)
    (effects : MixedMemoryEffects data initial cells)
    (ram : ExternalBoundary.WorkerRAM.Binding data.workers.rows)
    (commands : BigintCommands data) (hashes : HashCommands data)
    (member : worker ∈ data.workers.rows)
    (history : SailHistory historyCells events before after)
    (permutation : events.Perm (worker.memorySteps.map transferEvent))
    (observed : ∀ port ∈ worker.ports, ∃ cell : Cell,
      cell.addressCode = port.address.code worker.assignment ∧
        cell.read before = .ok (readToken worker.assignment port).word.toBitVec before) :
    FullCall worker.family before after := by
  cases worker with
  | mk family w =>
    cases family with
    | bigint =>
      exact path_worker_call_of_binding accepted inputs effects ram commands .bigint member rfl trivial
        history permutation observed
    | blakeG =>
      obtain ⟨reduced, index, control⟩ := hashes.gControl w member
      have pointers : PathGPointerBinding ⟨.blakeG, w⟩ :=
        hashes.gBases w member
      exact path_worker_call_of_binding accepted inputs effects ram commands (.hash ⟨.blakeG reduced, index⟩)
        member ⟨rfl, control⟩ pointers history permutation observed
    | blakeRound =>
      obtain ⟨flags, index, bound, control⟩ := hashes.roundControl w member
      exact path_worker_call_of_binding accepted inputs effects ram commands (.hash ⟨.blakeRound flags, ⟨index.val, bound⟩⟩)
        member ⟨rfl, control⟩ trivial history permutation observed
    | keccak =>
      obtain ⟨index, control⟩ := hashes.keccakControl w member
      exact path_worker_call_of_binding accepted inputs effects ram commands (.hash ⟨.keccak, index⟩)
        member ⟨rfl, control⟩ trivial history permutation observed

end Airbender.UnifiedReduced.Caller.Stream.Proofs
