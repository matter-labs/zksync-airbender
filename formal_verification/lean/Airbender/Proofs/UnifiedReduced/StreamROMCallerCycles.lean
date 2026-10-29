import Airbender.Proofs.UnifiedReduced.StreamROMNativeCalls
import Airbender.Proofs.UnifiedReduced.StreamROMExecution
import Airbender.Proofs.UnifiedReduced.NativePathExecution

namespace Airbender.UnifiedReduced.Caller.Stream.Proofs
open Arithmetic Trace Trace.Proofs Reference.RiscV.Sail Reference.Sail
open Caller.Proofs
set_option warningAsError true
set_option Elab.async false

/-- A caller's public bytes remain its source at the actual cycle boundary. -/
theorem caller_source_readonly
    {data : RequestTrace babyBearModulus}
    {initial before : State} {ca : List (BitVec 32)} {cells : List Cell}
    {events : List MemoryAccess}
    (accepted : RequestChecks data) (inputs : RequestInputs data initial ca)
    (code : ∀ entry ∈ data.program, entry.pc.toNat < ROM.limit ∧ entry.pc.toNat % 4 = 0)
    (unchanged : ∀ event ∈ events, ∀ pc : BitVec 32, pc.toNat < ROM.limit →
      event.2.1 = (Cell.ram pc).addressCode → event.2.2.1 = event.2.2.2)
    {row : Trace.Row babyBearModulus UnifiedFamily} (member : row ∈ data.callers)
    (past : SailHistory cells
      (events.filter fun event => decide (event.1 ≤ row.clock)) initial before) :
    ∃ entry ∈ data.program, row.decoderQuery = Delegation.Caller.query entry ∧
      row.start.word.toBitVec = entry.pc ∧
      entry.SourceWith (retiredState before row.start.word.toBitVec)
        Delegation.Caller.decoderFields := by
  have decoded := accepted.decoded row member
  change ∃ i : Fin data.program.length,
    row.decoderQuery = Delegation.Caller.query (data.program.get i) at decoded
  obtain ⟨i, query⟩ := decoded
  let entry := data.program.get i
  have present : entry ∈ data.program := List.get_mem _ _
  have source := run_program_sources inputs.image entry present
  have pcWord : row.start.word = Word.ofBitVec entry.pc := by
    have low := congrArg (fun values : Vector (ZMod babyBearModulus) 9 => values[0]) query
    have high := congrArg (fun values : Vector (ZMod babyBearModulus) 9 => values[1]) query
    cases row with
    | mk family assignment =>
      cases family
      exact word_of_pc_query (by decide) low high
  have pc := (congrArg Word.toBitVec pcWord).trans (Word.ofBitVec_roundtrip _)
  exact ⟨entry, present, query, pc,
    cycle_source_of_readonly past source unchanged (code entry present) pc⟩

/-- Native workers retire the caller at its exact shared-history boundaries. -/
theorem native_full_caller_cycle_at_readonly
    {data : RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry} {initial : State}
    {ca oa : List (BitVec 32)} {cells : List Cell}
    (accepted : MixedMemoryAccepted data program) (inputs : NativeMemoryInputsWith Stream.decoderFields data program initial ca oa cells)
    {events : List MemoryAccess}
    (code : ∀ entry ∈ data.program, entry.pc.toNat < ROM.limit ∧ entry.pc.toNat % 4 = 0)
    (unchanged : ∀ event ∈ events, ∀ pc : BitVec 32, pc.toNat < ROM.limit →
      event.2.1 = (Cell.ram pc).addressCode → event.2.2.1 = event.2.2.2)
    (ram : ExternalBoundary.WorkerRAM.Binding data.workers.rows) (commands : BigintCommands data)
    (hashes : HashCommands data)
    (effects : MixedMemoryEffects data initial cells)
    {finalState : State}
    (permutation : events.Perm (data.mixedSteps.map transferEvent))
    (order : events.Pairwise (fun a b => b.1 ≤ a.1))
    (history : SailHistory cells events initial finalState)
    {row : Trace.Row babyBearModulus UnifiedFamily} (member : row ∈ data.callers) :
    FullCallerCycle data initial finalState cells events row := by
  have nativeMember := List.mem_of_mem_filter member
  have clocks := machine_clock_facts (by decide) (by decide) accepted.toRequestChecks inputs.publicProgram nativeMember
  have floor := machine_native_clock_positive (by decide) (by decide) accepted
    inputs.publicProgram inputs.initialization nativeMember
  have positive : 0 < Delegation.Caller.startClock row := by omega
  obtain ⟨before, after, _, past, current, future⟩ := history_window order history
    (by omega : Delegation.Caller.startClock row ≤ Delegation.Caller.finishClock row)
  have cycle := cycle_window_permutation (by decide) (by decide) accepted.toRequestChecks inputs.publicProgram
    effects.requests permutation nativeMember positive
  obtain ⟨worker, present, matched, grouped, localHistory⟩ :=
    caller_cycle_worker_history effects.requests member cycle current
  have readable := history_cells_readable past inputs.aligned (by
    intro cell included
    obtain ⟨_, _, value, read, _⟩ := image_cell_source inputs.initialization cell included
    exact ⟨value, read⟩)
  have noZero : ∀ event ∈ (events.filter (fun event => decide
      (Delegation.Caller.startClock row < event.1 ∧ event.1 ≤ Delegation.Caller.finishClock row))).filter
        (fun event => decide (event.2.1 ≠ (Cell.register 0).addressCode)),
      event.2.1 ≠ (Cell.register 0).addressCode := by
    intro event included
    exact of_decide_eq_true (List.mem_filter.mp included).2
  have distinct := (grouped.map (fun event => event.2.1)).nodup_iff.mpr (by
    simpa only [List.map_map, Function.comp_def, transferEvent] using
      worker_addresses_distinct accepted inputs effects present)
  have actual := Delegation.Proofs.atomic_observations localHistory inputs.aligned noZero readable distinct
  have observed : ∀ port ∈ worker.ports, ∃ cell : Cell,
      cell.addressCode = port.address.code worker.assignment ∧
        cell.read before = .ok (readToken worker.assignment port).word.toBitVec before := by
    intro port included
    have event := grouped.mem_iff.mpr (List.mem_map.mpr ⟨_, List.mem_map.mpr
      ⟨port, by simpa using included, rfl⟩, rfl⟩)
    obtain ⟨cell, _, address, read, _⟩ := actual _ event
    exact ⟨cell, address, read⟩
  have raw := native_worker_call_of_binding accepted inputs effects ram commands hashes present localHistory grouped observed
  have rebased := native_worker_call_of_binding accepted inputs effects ram commands hashes present
    (retired_state_history localHistory row.start.word.toBitVec) grouped (fun port included => by
      obtain ⟨cell, address, read⟩ := observed port included
      exact ⟨cell, address, cell_read_PC cell (cell_read_nextPC cell read _) _⟩)
  obtain ⟨entry, included, query, pc, source⟩ :=
    caller_source_readonly accepted.toRequestChecks inputs.publicProgram code unchanged member past
  have original : entry.SourceWith before Delegation.Caller.decoderFields :=
    ⟨read_word_frame (before := retiredState before row.start.word.toBitVec) (after := before) rfl source.bytes,
      (decoded_misa_frame _ source.decoded).2 _ (by simp [retiredState, Std.ExtDHashMap.get?_insert]), source.fields⟩
  have family := caller_worker_family (by decide) query matched
  exact ⟨before, after, past, current, future, entry, included, query, pc, original,
    family ▸ raw, _, family ▸ rebased, caller_pc_retirement effects.requests member⟩


/-- Native combined execution under explicit worker input and physical-code contracts. -/
theorem native_path_execution_interpreted [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]
    {data : RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry}
    {initial : State} {ca oa : List (BitVec 32)} {cells : List Cell}
    (accepted : MixedMemoryAccepted data program)
    (inputs : NativeMemoryInputsWith Stream.decoderFields data program initial ca oa cells)
    (profile : Stream.ROMProfile data program initial cells)
    (rawRows : ∀ w, (⟨.machine, w⟩ : Trace.Row babyBearModulus UnifiedFamily) ∈ data.machine.rows →
      ∃ raw, FlatOperation.ConstraintsHoldFlat (Verification.environment raw)
        (importedConstraints (Setup.table initial)) ∧ raw 4 = 1 ∧
        w = (ROMView.row initial (⟨.machine, raw⟩ : Trace.Row babyBearModulus UnifiedFamily)).assignment)
    (ram : ExternalBoundary.WorkerRAM.Binding data.workers.rows)
    (readonly : ∀ event ∈ data.mixedSteps.map transferEvent, ∀ pc : BitVec 32, pc.toNat < ROM.limit →
      event.2.1 = (Cell.ram pc).addressCode → event.2.2.1 = event.2.2.2)
    (pc : run (SailRV32.Functions.get_arch_pc ()) initial =
      .ok data.machine.initial.word.toBitVec initial)
    (commands : BigintCommands data) (hashes : HashCommands data)
    (stream : List (BitVec 32)) (ports : Stream.StreamPorts data.machine stream) :
    Stream.Realizes stream program data.program data.machine initial cells := by
  have effects := native_memory_effects accepted inputs hashes
  have ledger := ExternalBoundary.Requests.Proofs.native_binding
    accepted.toRequestChecks effects.requests
  obtain ⟨events, finalState, permutation, order, history, _, _, terminal⟩ := effects.execution
  have unchanged : ∀ event ∈ events, ∀ pc : BitVec 32, pc.toNat < ROM.limit →
      event.2.1 = (Cell.ram pc).addressCode → event.2.2.1 = event.2.2.2 :=
    fun event member => readonly event (permutation.mem_iff.mp member)
  exact execution_at_readonly accepted inputs profile.ordinaryCode unchanged effects.requests pc ledger
    permutation order history stream
    (fun _ member ordinary => ordinary_cycle_at_interpreted accepted inputs profile rawRows effects
      permutation order history stream ports member ordinary)
    (fun _ member => native_full_caller_cycle_at_readonly accepted inputs profile.callerCode unchanged ram commands
      hashes effects permutation order history member) terminal

end Airbender.UnifiedReduced.Caller.Stream.Proofs
