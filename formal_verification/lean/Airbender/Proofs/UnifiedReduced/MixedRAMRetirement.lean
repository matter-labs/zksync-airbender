import Airbender.Proofs.UnifiedReduced.MixedRetirement
import Airbender.Proofs.UnifiedReduced.MemoryExecution

namespace Airbender.UnifiedReduced.Caller.Proofs
open Arithmetic Reference.RiscV Reference.RiscV.Sail Reference.Sail Trace Trace.Proofs
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

theorem word_fields {input : Airbender.WordMemory.Input} {entry : UnifiedReduced.ProgramEntry}
    (fields : Mixed.decoderFields entry.instruction = some entry.data)
    (encoding : entry.instruction = if input.store then .STORE (input.encodedImmediate, input.rs2, input.rs1, 4)
      else .LOAD (input.encodedImmediate, input.rs1, input.rd, false, 4)) :
    UnifiedReduced.decoderFields entry.instruction = some entry.data := by
  rcases Mixed.Proofs.fields_cases fields with standard | custom
  · exact standard
  · rw [encoding] at custom
    cases mode : input.store <;> simp [mode, customDecoderFields] at custom

theorem mixed_ram_cycle [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]
    {data : RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry}
    {initial : State} {ca oa : List (BitVec 32)} {cells : List Cell}
    (accepted : MixedMemoryAccepted data program) (inputs : MixedMemoryInputs data program initial ca oa cells)
    (started : 0 < (timeOfPair data.machine.initial.timestamp).value)
    (configuration : FlatMemoryConfiguration initial)
    (ordinary : ∀ address, Cell.ram address ∈ cells → OrdinaryWordAddress address)
    (ram : ∀ address, Cell.ram address ∈ cells → 4194304 ≤ address.toNat)
    {w : Nat → ZMod babyBearModulus} {input : Airbender.WordMemory.Input} {output : Airbender.WordMemory.Output}
    (destination : input.store = false → input.rd ≠ zeroRegister)
    (member : (⟨.machine, w⟩ : Trace.Row babyBearModulus UnifiedFamily) ∈ data.machine.rows)
    (words : WordMemory.WordMapping input output w)
    (instruction : ∃ entry ∈ program, decoderQuery w = entry.query ∧
      entry.instruction = if input.store then .STORE (input.encodedImmediate, input.rs2, input.rs1, 4)
        else .LOAD (input.encodedImmediate, input.rs1, input.rd, false, 4)) :
    ∃ events finalState,
      events.Perm (data.mixedSteps.map transferEvent) ∧
      SailHistory cells events initial finalState ∧
      RetiresCycle cells events initial finalState (⟨.machine, w⟩ : Trace.Row babyBearModulus UnifiedFamily)
        (Airbender.WordMemory.execution input) := by
  obtain ⟨entry, present, query, encoding⟩ := instruction
  have source := run_program_sources inputs.ordinaryProgram entry present
  have fields := word_fields source.fields encoding
  have core := Verification.holds_of_sublist (accepted.constraints _ member)
    (List.sublist_append_left (importedConstraints data.machine.rom) importedConstraintsTimestampLookups)
  have metadata := WordMemory.Proofs.decoded_metadata fields encoding destination
  have ordinaryRow : (⟨.machine, w⟩ : Trace.Row babyBearModulus UnifiedFamily) ∉ data.callers := by
    apply ordinary_of_decoder_mask (by decide) core fields query
    rw [metadata]
    cases mode : input.store <;> simp [WordMemory.Proofs.metadata, mode, Nat.testBit, Nat.shiftRight_eq_div_pow]
  obtain ⟨events, finalState, before, after, permutation, history, past, current, future, native, ranges⟩ :=
    ordinary_cycle_context accepted inputs started member ordinaryRow
  have sourceRange := ranges importedConstraintsMemoryPorts[0]
    (by simp [Trace.Row.ports, CircuitLayout.ports, importedConstraintsMemoryPorts])
  let actualInput : Airbender.WordMemory.Input := {input with before := retiredState before (Control.initialPC w).toBitVec}
  have actualWords : WordMemory.WordMapping actualInput output w :=
    ⟨words.sourceLo, words.sourceHi, words.immediateLo, words.immediateHi, words.readLo, words.readHi,
      words.addressLo, words.addressHi, words.dataLo, words.dataHi, words.pcLo, words.pcHi,
      words.finalPCLo, words.finalPCHi⟩
  have pcWord : input.pc = Control.initialPC w := congrArg₂ Word.mk words.pcLo words.pcHi
  have pcRead : run (SailRV32.Functions.get_arch_pc ()) actualInput.before =
      .ok actualInput.pc.toBitVec actualInput.before := by
    rw [show actualInput.pc = Control.initialPC w from pcWord]
    exact retired_state_pc before _
  have copied := WordMemory.Proofs.ram_copy_from_history (by decide) core native actualWords fields query encoding destination ram
  have spec := WordMemory.Proofs.row_soundness_from_history (by decide) core (accepted.active _ member)
    (by simpa only [actualInput, pcWord] using retired_state_history past (Control.initialPC w).toBitVec)
    (retired_state_history native (Control.initialPC w).toBitVec) sourceRange actualWords fields query encoding
    configuration (fun address present => inputs.aligned (.ram address) present) ordinary destination copied pcRead
  have retired := UnifiedReduced.Proofs.word_register_retirement (by decide) (input := actualInput) core fields query encoding destination actualWords rfl native spec
  refine ⟨events, finalState, permutation, history, before, after, past, current, future, ?_⟩
  simpa [Airbender.WordMemory.execution, actualInput, Trace.Row.start, Trace.Row.finish, Trace.Row.columns,
    CircuitLayout.columns, PCState.State.word, rawPair, importedConstraintsTraceColumns,
    Control.initialPC, Control.finalPC] using retired

end Airbender.UnifiedReduced.Caller.Proofs
