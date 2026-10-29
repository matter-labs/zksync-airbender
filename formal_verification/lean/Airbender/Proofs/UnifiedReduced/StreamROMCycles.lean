import Airbender.Proofs.UnifiedReduced.StreamOrdinaryCycles
import Airbender.Proofs.UnifiedReduced.ROMCopy

namespace Airbender.UnifiedReduced.Caller.Stream.Proofs
open Arithmetic Reference.RiscV Reference.RiscV.Sail Reference.Sail Trace Trace.Proofs
open Caller.Proofs
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

/-- Native ROM interpretation proves load/store retirement without a global RAM bound. -/
theorem ram_cycle_at_interpreted [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]
    {data : RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry}
    {initial : State} {ca oa : List (BitVec 32)} {cells : List Cell}
    (accepted : MixedMemoryAccepted data program) (inputs : NativeMemoryInputsWith Stream.decoderFields data program initial ca oa cells)
    (effects : MixedMemoryEffects data initial cells)
    {events : List MemoryAccess} {finalState : State}
    (permutation : events.Perm (data.mixedSteps.map transferEvent))
    (order : events.Pairwise (fun a b => b.1 ≤ a.1))
    (history : SailHistory cells events initial finalState)
    (configuration : FlatMemoryConfiguration initial)
    (ordinary : ∀ address, Cell.ram address ∈ cells → PlatformWordAddress address)
    {raw : Nat → ZMod babyBearModulus}
    (rawCore : FlatOperation.ConstraintsHoldFlat (Verification.environment raw)
      (importedConstraints (Setup.table initial)))
    (rawActive : raw 4 = 1)
    {w : Nat → ZMod babyBearModulus} {input : Airbender.WordMemory.Input} {output : Airbender.WordMemory.Output}
    (interpreted : w = (ROMView.row initial
      (⟨.machine, raw⟩ : Trace.Row babyBearModulus UnifiedFamily)).assignment)
    (destination : input.store = false → input.rd ≠ zeroRegister)
    (member : (⟨.machine, w⟩ : Trace.Row babyBearModulus UnifiedFamily) ∈ data.machine.rows)
    (words : WordMemory.WordMapping input output w)
    (instruction : ∃ entry ∈ program, entry.SourceWith initial Mixed.decoderFields ∧
      decoderQuery w = entry.query ∧
      entry.instruction = if input.store then .STORE (input.encodedImmediate, input.rs2, input.rs1, 4)
        else .LOAD (input.encodedImmediate, input.rs1, input.rd, false, 4)) :
      RetiresCycle cells events initial finalState (⟨.machine, w⟩ : Trace.Row babyBearModulus UnifiedFamily)
        (Airbender.WordMemory.execution input) := by
  obtain ⟨entry, present, source, query, encoding⟩ := instruction
  have fields := word_fields source.fields encoding
  have core := Verification.holds_of_sublist (accepted.constraints _ member)
    (List.sublist_append_left (importedConstraints data.machine.rom) importedConstraintsTimestampLookups)
  have metadata := WordMemory.Proofs.decoded_metadata fields encoding destination
  have ordinaryRow : (⟨.machine, w⟩ : Trace.Row babyBearModulus UnifiedFamily) ∉ data.callers := by
    apply ordinary_of_decoder_mask (by decide) core fields query
    rw [metadata]
    cases mode : input.store <;> simp [WordMemory.Proofs.metadata, mode, Nat.testBit, Nat.shiftRight_eq_div_pow]
  obtain ⟨before, after, past, current, future, native, ranges⟩ :=
    ordinary_context_at accepted inputs effects permutation order history member ordinaryRow
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
  have dataFields := WordMemory.Proofs.decoded_metadata fields encoding destination
  have rawQuery : decoderQuery raw = entry.query := by
    have preserved := ROMView.row_query initial
      (⟨.machine, raw⟩ : Trace.Row babyBearModulus UnifiedFamily)
    change decoderQuery (ROMView.row initial
      (⟨.machine, raw⟩ : Trace.Row babyBearModulus UnifiedFamily)).assignment = decoderQuery raw at preserved
    rw [← interpreted] at preserved
    exact preserved.symm.trans query
  have rawFlags := UnifiedReduced.Proofs.decoder_selectors (by decide) rawCore
    (UnifiedReduced.Proofs.decoder_field_bounds fields).2.1 rawQuery
  have rawLoad : raw 28 = if input.store then 0 else 1 := by
    have flag := rawFlags 17
    rw [dataFields] at flag
    cases mode : input.store <;> simpa [WordMemory.Proofs.metadata, mode,
      importedConstraintsDecoderColumns, Nat.testBit, Nat.shiftRight_eq_div_pow] using flag
  have rawStore : raw 29 = if input.store then 1 else 0 := by
    have flag := rawFlags 18
    rw [dataFields] at flag
    cases mode : input.store <;> simpa [WordMemory.Proofs.metadata, mode,
      importedConstraintsDecoderColumns, Nat.testBit, Nat.shiftRight_eq_div_pow] using flag
  have nativeCopy := ROMView.row_word_copy (by decide) input.store rawCore rawActive rawLoad rawStore
  have copied : output.data.toBitVec = input.readData.toBitVec := by
    have outputWord : output.data = Word.mk (w 50).val (w 51).val :=
      congrArg₂ Word.mk words.dataLo words.dataHi
    have inputWord : input.readData = Word.mk (w 42).val (w 43).val :=
      congrArg₂ Word.mk words.readLo words.readHi
    simpa only [outputWord, inputWord, interpreted] using nativeCopy
  have spec := WordMemory.Proofs.row_soundness_from_history (by decide) core (accepted.active _ member)
    (by simpa only [actualInput, pcWord] using retired_state_history past (Control.initialPC w).toBitVec)
    (retired_state_history native (Control.initialPC w).toBitVec) sourceRange actualWords fields query encoding
    configuration (fun address present => inputs.aligned (.ram address) present) ordinary destination copied pcRead
  have retired := UnifiedReduced.Proofs.word_register_retirement (by decide) (input := actualInput) core fields query encoding destination actualWords rfl native spec
  refine ⟨before, after, past, current, future, ?_⟩
  simpa [Airbender.WordMemory.execution, Airbender.WordMemory.instruction, Trace.instructionClause, Option.get_some, actualInput, Trace.Row.start, Trace.Row.finish, Trace.Row.columns,
    CircuitLayout.columns, PCState.State.word, rawPair, importedConstraintsTraceColumns,
    Control.initialPC, Control.finalPC] using retired

end Airbender.UnifiedReduced.Caller.Stream.Proofs
