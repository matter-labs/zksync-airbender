import Airbender.Proofs.Reduced.PrefixBoundary
import Airbender.Proofs.Reduced.SupportedRound
import Airbender.Proofs.Trace.ExternalStream

namespace Airbender.AddSub.Modular.External.Caller.Proofs
open Trace Arithmetic Trace.Proofs Reference.RiscV.Sail Reference.Sail
open Delegation.Caller Delegation.Caller.Proofs
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

/-- Cutting before a native instruction retains each external response binding. -/
theorem supported_prefix_stream_ports
    {data : RequestTrace babyBearModulus} {stream : List (BitVec 32)}
    (ports : External.StreamPorts data.machine stream)
    (point : PCState.State babyBearModulus) (memory : List (MemoryToken babyBearModulus)) :
    External.StreamPorts (supportedPrefix data point memory).machine stream :=
  ExternalStream.Proofs.ports_before Trace.Row.clock External.isRead External.response
    data.machine.rows (timeOfPair point.timestamp).value ports

private theorem supported_caller_entry
    {data : RequestTrace babyBearModulus} {program : List PooledProgramEntry}
    (accepted : MixedMemoryAccepted data program)
    {caller : Trace.Row babyBearModulus PooledFamily} (called : caller ∈ data.callers) :
    ∃ entry ∈ data.program, Delegation.Caller.nativeQuery caller.assignment = Delegation.Caller.query entry ∧
      caller.start.word.toBitVec = entry.pc := by
  have decoded := accepted.decoded caller called
  change ∃ i : Fin data.program.length,
    Delegation.Caller.nativeQuery caller.assignment = Delegation.Caller.query (data.program.get i) at decoded
  obtain ⟨i, query⟩ := decoded
  have family := (caller_member called).2
  have word : caller.start.word = Word.ofBitVec (data.program.get i).pc := by
    have native := Delegation.Caller.Proofs.query_pc (by decide) query
    cases caller with
    | mk kind w => cases family; exact native
  exact ⟨data.program.get i, List.get_mem _ _, query,
    (congrArg Word.toBitVec word).trans (Word.ofBitVec_roundtrip _)⟩

/-- Native prefixes derive round controls and port locations from public supported use. -/
theorem supported_native_worker_inputs [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]
    {data : RequestTrace babyBearModulus} {program : ReducedUse.Program}
    {initial : State} {cells : List Cell}
    (accepted : MixedMemoryAccepted data program.ordinary)
    (boot : PooledBootInputs data.machine initial cells program.ordinary Caller.reducedDecoderFields)
    (callers : ∃ addresses, Delegation.Caller.programImage initial addresses = some data.program)
    (tables : data.workers.setup = Delegation.modeledSetup Keccak.Controller.rows)
    (code : ∀ entry ∈ data.program, entry.pc.toNat < ROM.limit ∧ entry.pc.toNat % 4 = 0)
    (families : ∀ row ∈ data.machine.rows, Caller.reducedFamily row.family = true)
    (workerFamilies : ∀ worker ∈ data.workers.rows, worker.family = .blakeRound)
    (registry : data.program = program.callers) (valid : ReducedUse.ValidDelegationUse program initial)
    (stream : List (BitVec 32)) (ports : External.StreamPorts data.machine stream) :
    ∀ worker ∈ data.workers.rows, ExternalBoundary.HashABI.RoundControl worker.assignment ∧
      ∀ port ∈ worker.ports, ∃ location : ExternalBoundary.WorkerRAM.Location,
        port.address.code worker.assignment = location.cell.addressCode := by
  obtain ⟨ca, callerImage⟩ := callers
  have clocks := ROMView.native_clocks (by decide) boot.seed boot.initialBoundary
  have publicProgram : RequestInputs data initial ca := ⟨callerImage, clocks.initial, clocks.aligned⟩
  have seed := native_seed_clocks boot
  have requests := request_binding_checks (by decide) (by decide) (by decide)
    accepted.toRequestChecks publicProgram
  have schedule := worker_schedule (by decide) (by decide) accepted.toRequestChecks publicProgram requests
  have positive : 0 < (timeOfPair data.machine.initial.timestamp).value := by
    rw [boot.initialBoundary]
    norm_num [PCState.boundary, timeOfPair, Timestamp.value, babyBearModulus]
    decide
  have allowed : ∀ entry ∈ data.program, Caller.reducedCall entry.data.family := by
    intro entry member
    obtain ⟨_, _, _, _, family⟩ := valid.shapes.coverage entry (registry ▸ member)
    exact family
  have next : ∀ clock, ∀ caller ∈ data.callers, Delegation.Caller.startClock caller = clock →
      ∀ worker ∈ data.workers.rows,
        Delegation.Requests.fulfillment worker = Delegation.Requests.caller caller.assignment →
        Delegation.Caller.WorkerSlot caller worker →
        ExternalBoundary.HashABI.RoundControl worker.assignment ∧
          ∀ port ∈ worker.ports, ∃ location : ExternalBoundary.WorkerRAM.Location,
            port.address.code worker.assignment = location.cell.addressCode := by
    intro clock
    induction clock using Nat.strong_induction_on with
    | h clock ih =>
      intro caller called current worker member _matched slot
      obtain ⟨memory, prefixAccepted, suffix⟩ := supported_prefix_accepted_native
        accepted publicProgram seed positive (List.mem_of_mem_filter called)
      let prefixData := supportedPrefix data caller.start memory
      have earlier : ∀ previous ∈ prefixData.workers.rows,
          ExternalBoundary.HashABI.RoundControl previous.assignment ∧
            ∀ port ∈ previous.ports, ∃ location : ExternalBoundary.WorkerRAM.Location,
              port.address.code previous.assignment = location.cell.addressCode := by
        intro previous included
        have original := (List.mem_filter.mp included).1
        have boundary := of_decide_eq_true (List.mem_filter.mp included).2
        have live := Delegation.Proofs.active_invocation_live
          (accepted.workerConstraints previous original) (accepted.workerActive previous original)
        obtain ⟨other, otherCalled, otherMatch, otherSlot⟩ := live_worker_slot schedule original live
        have time : workerClock previous = Delegation.Caller.startClock other + 4 := by
          dsimp only [workerClock]
          rw [otherSlot.invocation]
        have less : Delegation.Caller.startClock other < clock := by
          change workerClock previous ≤ Delegation.Caller.startClock caller at boundary
          omega
        exact ih _ less other otherCalled rfl previous original otherMatch otherSlot
      have prefixRAM : ExternalBoundary.WorkerRAM.Binding prefixData.workers.rows :=
        fun previous included => (earlier previous included).2
      have controls : ∀ w, (⟨.blakeRound, w⟩ : Delegation.Row babyBearModulus) ∈ prefixData.workers.rows →
          ExternalBoundary.HashABI.RoundControl w := fun _ included => (earlier _ included).1
      have prefixBoot := supported_prefix_boot accepted publicProgram boot
        (List.mem_of_mem_filter called) prefixAccepted
      have prefixFamilies : ∀ row ∈ prefixData.machine.rows, Caller.reducedFamily row.family = true :=
        fun row included => families row (List.mem_of_mem_filter included)
      have prefixWorkerFamilies : ∀ previous ∈ prefixData.workers.rows, previous.family = .blakeRound :=
        fun previous included => workerFamilies previous (List.mem_of_mem_filter included)
      have prefixPorts := supported_prefix_stream_ports ports caller.start memory
      obtain ⟨state, execution, atPC, terminal⟩ := native_rom_path_execution prefixAccepted prefixBoot
        ⟨ca, callerImage⟩ tables code allowed prefixFamilies prefixWorkerFamilies prefixRAM controls stream prefixPorts
      have reachable : ReducedUse.Reachable stream program initial
          (state, External.readCount prefixData.machine) := by
        simpa only [ReducedUse.Reachable, prefixData, supportedPrefix, registry] using execution
      obtain ⟨entry, registered, _query, entryPC⟩ := supported_caller_entry accepted called
      have publicEntry : entry ∈ program.callers := registry ▸ registered
      have publicPC : UnifiedReduced.Caller.DelegationUse.AtPC state entry.pc := by
        change run (SailRV32.Functions.get_arch_pc ()) state = .ok entry.pc state
        change run (SailRV32.Functions.get_arch_pc ()) state = .ok caller.start.word.toBitVec state at atPC
        exact entryPC ▸ atPC
      have frontier (port : MemoryPort) (present : port ∈ worker.ports) :
          readToken worker.assignment port ∈ memory :=
        supported_prefix_worker_read_native accepted publicProgram seed positive called member slot suffix present
      have prefixInputs : RequestInputs prefixData initial ca :=
        ⟨callerImage, clocks.initial, clocks.aligned⟩
      have prefixRequests := request_binding_checks (by decide) (by decide) (by decide)
        prefixAccepted.toRequestChecks prefixInputs
      have prefixFacts := native_memory_facts (by decide) (by decide) prefixAccepted prefixInputs seed prefixRequests
      have physicalAccepted := NativeROM.Proofs.accepted (by decide) initial
        prefixAccepted prefixRequests prefixFacts boot.seed prefixRAM
      obtain ⟨pca, poa, physicalInputs⟩ := interpreted_inputs (by decide) prefixBoot ⟨ca, callerImage⟩ tables
      have effects := mixed_memory_effects physicalAccepted physicalInputs
        (native_round_masks physicalAccepted physicalInputs controls)
      have core := accepted.workerConstraints worker member
      rw [tables] at core
      apply supported_round_and_ram_of_reference stream (External.readCount prefixData.machine)
        valid reachable publicEntry publicPC (workerFamilies worker member) core
      · intro port present
        exact effects.terminal _ (List.mem_map.mpr ⟨_, frontier port present, rfl⟩)
      · intro port present
        obtain ⟨cell, _, address, read⟩ := terminal _ (frontier port present)
        exact ⟨cell, address, read⟩
  intro worker member
  have live := Delegation.Proofs.active_invocation_live
    (accepted.workerConstraints worker member) (accepted.workerActive worker member)
  obtain ⟨caller, called, matched, slot⟩ := live_worker_slot schedule member live
  exact next _ caller called rfl worker member matched slot

/-- Public supported use closes the remaining private native worker input contracts. -/
theorem supported_native_path_execution [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]
    {data : RequestTrace babyBearModulus} {program : ReducedUse.Program}
    {initial : State} {cells : List Cell}
    (accepted : MixedMemoryAccepted data program.ordinary)
    (boot : PooledBootInputs data.machine initial cells program.ordinary Caller.reducedDecoderFields)
    (callers : ∃ addresses, Delegation.Caller.programImage initial addresses = some data.program)
    (tables : data.workers.setup = Delegation.modeledSetup Keccak.Controller.rows)
    (code : ∀ entry ∈ data.program, entry.pc.toNat < ROM.limit ∧ entry.pc.toNat % 4 = 0)
    (families : ∀ row ∈ data.machine.rows, Caller.reducedFamily row.family = true)
    (workerFamilies : ∀ worker ∈ data.workers.rows, worker.family = .blakeRound)
    (registry : data.program = program.callers) (valid : ReducedUse.ValidDelegationUse program initial)
    (stream : List (BitVec 32)) (ports : External.StreamPorts data.machine stream) :
    Caller.ReducedRealizes stream program.ordinary program.callers data.machine initial cells (ROMView.token initial) := by
  have good := supported_native_worker_inputs accepted boot callers tables code families workerFamilies registry valid stream ports
  have ram : ExternalBoundary.WorkerRAM.Binding data.workers.rows := fun worker member => (good worker member).2
  have controls : ∀ w, (⟨.blakeRound, w⟩ : Delegation.Row babyBearModulus) ∈ data.workers.rows →
      ExternalBoundary.HashABI.RoundControl w := fun _ member => (good _ member).1
  have allowed : ∀ entry ∈ data.program, Caller.reducedCall entry.data.family := by
    intro entry member
    obtain ⟨_, _, _, _, family⟩ := valid.shapes.coverage entry (registry ▸ member)
    exact family
  simpa only [registry] using native_rom_path_execution accepted boot callers tables code allowed families
    workerFamilies ram controls stream ports

end Airbender.AddSub.Modular.External.Caller.Proofs
