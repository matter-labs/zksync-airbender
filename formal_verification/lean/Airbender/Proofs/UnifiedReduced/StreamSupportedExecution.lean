import Airbender.Proofs.UnifiedReduced.StreamCallerCycles
import Airbender.Proofs.UnifiedReduced.StreamSupportedControls
import Airbender.Proofs.UnifiedReduced.StreamPrefix

namespace Airbender.UnifiedReduced.Caller.Stream.Proofs
open Arithmetic Trace Trace.Proofs Reference.RiscV.Sail Reference.Sail
open Caller.Proofs
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

private theorem supported_commands {data : RequestTrace babyBearModulus}
    (workers : ∀ worker ∈ data.workers.rows, SupportedWorker worker) :
    BigintCommands data ∧ HashCommands data := by
  refine ⟨?_, ⟨?_, ?_, ?_, ?_⟩⟩
  · intro worker member family
    have good := workers worker member
    simpa only [SupportedWorker, family] using good
  · intro w member; exact (workers ⟨.blakeG, w⟩ member).1
  · intro w member; exact (workers ⟨.blakeG, w⟩ member).2
  · intro w member; exact workers ⟨.blakeRound, w⟩ member
  · intro w member; exact False.elim (workers ⟨.keccak, w⟩ member)

private theorem supported_caller_entry
    {data : RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry}
    (accepted : MixedMemoryAccepted data program)
    {caller : Trace.Row babyBearModulus UnifiedFamily} (called : caller ∈ data.callers) :
    ∃ entry ∈ data.program, caller.decoderQuery = Delegation.Caller.query entry ∧
      caller.start.word.toBitVec = entry.pc := by
  have decoded := accepted.decoded caller called
  change ∃ i : Fin data.program.length,
    caller.decoderQuery = Delegation.Caller.query (data.program.get i) at decoded
  obtain ⟨i, query⟩ := decoded
  let entry := data.program.get i
  have word : caller.start.word = Word.ofBitVec entry.pc := by
    have low := congrArg (fun values : Vector (ZMod babyBearModulus) 9 => values[0]) query
    have high := congrArg (fun values : Vector (ZMod babyBearModulus) 9 => values[1]) query
    cases caller with
    | mk kind w => cases kind; exact word_of_pc_query (by decide) low high
  exact ⟨entry, List.get_mem _ _, query,
    (congrArg Word.toBitVec word).trans (Word.ofBitVec_roundtrip _)⟩


/-- Earlier native prefixes derive controls before the next reference call. -/
theorem supported_worker_inputs [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]
    {data : RequestTrace babyBearModulus} {program : DelegationUse.Program}
    {initial : State} {ca oa : List (BitVec 32)} {cells : List Cell}
    (accepted : MixedMemoryAccepted data program.ordinary)
    (inputs : NativeMemoryInputsWith Stream.decoderFields data program.ordinary initial ca oa cells)
    (profile : RetirementProfile data program.ordinary initial cells)
    (pc : run (SailRV32.Functions.get_arch_pc ()) initial = .ok data.machine.initial.word.toBitVec initial)
    (registry : data.program = program.callers) (valid : Stream.ValidDelegationUse program initial)
    (stream : List (BitVec 32)) (ports : Stream.StreamPorts data.machine stream) :
    ∀ worker ∈ data.workers.rows, SupportedWorker worker := by
  have requests := request_binding (by decide) (by decide) accepted.toRequestChecks inputs.publicProgram
  have next : ∀ clock, ∀ caller ∈ data.callers, Delegation.Caller.startClock caller = clock →
      ∀ worker ∈ data.workers.rows,
        Delegation.Requests.fulfillment worker = request caller.assignment →
        Delegation.Caller.WorkerSlot caller worker → SupportedWorker worker := by
    intro clock
    induction clock using Nat.strong_induction_on with
    | h clock ih =>
      intro caller called current worker member matched slot
      obtain ⟨memory, prefixAccepted, suffix⟩ := supported_prefix_accepted accepted inputs.publicProgram
        inputs.initialization (List.mem_of_mem_filter called)
      let prefixData := supportedPrefix data caller.start memory
      have earlier : ∀ previous ∈ prefixData.workers.rows, SupportedWorker previous := by
        intro previous included
        have original := (List.mem_filter.mp included).1
        have boundary := of_decide_eq_true (List.mem_filter.mp included).2
        have live := Delegation.Proofs.active_invocation_live
          (accepted.workerConstraints previous original) (accepted.workerActive previous original)
        obtain ⟨other, otherCalled, otherMatch, otherSlot⟩ := live_worker_slot requests original live
        have time : workerClock previous = Delegation.Caller.startClock other + 4 := by
          dsimp only [workerClock]
          rw [otherSlot.invocation]
        have less : Delegation.Caller.startClock other < clock := by
          change workerClock previous ≤ Delegation.Caller.startClock caller at boundary
          omega
        exact ih _ less other otherCalled rfl previous original otherMatch otherSlot
      obtain ⟨commands, hashes⟩ := supported_commands earlier
      let prefixInputs := supported_prefix_inputs inputs caller.start memory
      let prefixProfile := supported_prefix_profile profile caller.start memory
      have prefixPorts := supported_prefix_stream_ports ports caller.start memory
      obtain ⟨state, execution, atPC, terminal⟩ := native_path_execution prefixAccepted
        prefixInputs prefixProfile pc commands hashes stream prefixPorts
      have reachable : Stream.Reachable stream program initial
          (state, Stream.readCount prefixData.machine) := by
        simpa only [Stream.Reachable, prefixData, supportedPrefix, registry] using execution
      obtain ⟨entry, registered, query, entryPC⟩ := supported_caller_entry accepted called
      have publicEntry : entry ∈ program.callers := registry ▸ registered
      have publicPC : DelegationUse.AtPC state entry.pc := by
        change run (SailRV32.Functions.get_arch_pc ()) state = .ok entry.pc state
        change run (SailRV32.Functions.get_arch_pc ()) state = .ok caller.start.word.toBitVec state at atPC
        exact entryPC ▸ atPC
      have frontier (port : MemoryPort) (present : port ∈ worker.ports) :
          readToken worker.assignment port ∈ memory :=
        supported_prefix_worker_read accepted inputs.publicProgram inputs.initialization called member slot suffix present
      have effects := native_memory_effects prefixAccepted prefixInputs hashes
      apply supported_worker_of_reference stream (Stream.readCount prefixData.machine) valid reachable publicEntry publicPC
        (caller_worker_family (by decide) query matched)
      · intro port present
        exact effects.terminal _ (frontier port present)
      · intro port present
        obtain ⟨cell, _, address, read⟩ := terminal _ (frontier port present)
        exact ⟨cell, address, read⟩
  intro worker member
  have live := Delegation.Proofs.active_invocation_live
    (accepted.workerConstraints worker member) (accepted.workerActive worker member)
  obtain ⟨caller, called, matched, slot⟩ := live_worker_slot requests member live
  exact next _ caller called rfl worker member matched slot


/-- Public supported use derives all worker contracts before native execution. -/
theorem supported_path_execution [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]
    {data : RequestTrace babyBearModulus} {program : DelegationUse.Program}
    {initial : State} {ca oa : List (BitVec 32)} {cells : List Cell}
    (accepted : MixedMemoryAccepted data program.ordinary)
    (inputs : NativeMemoryInputsWith Stream.decoderFields data program.ordinary initial ca oa cells)
    (profile : RetirementProfile data program.ordinary initial cells)
    (pc : run (SailRV32.Functions.get_arch_pc ()) initial = .ok data.machine.initial.word.toBitVec initial)
    (registry : data.program = program.callers) (valid : Stream.ValidDelegationUse program initial)
    (stream : List (BitVec 32)) (ports : Stream.StreamPorts data.machine stream) :
    Stream.Realizes stream program.ordinary program.callers data.machine initial cells := by
  obtain ⟨commands, hashes⟩ := supported_commands
    (supported_worker_inputs accepted inputs profile pc registry valid stream ports)
  simpa only [registry] using native_path_execution accepted inputs profile pc commands hashes stream ports

end Airbender.UnifiedReduced.Caller.Stream.Proofs
