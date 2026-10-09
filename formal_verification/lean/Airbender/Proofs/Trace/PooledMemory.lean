import Airbender.Proofs.Trace.PooledCode
import Airbender.Proofs.Trace.WordMemory

namespace Airbender.Trace.Proofs
open Arithmetic Reference.RiscV.Sail Reference.Sail

set_option backward.isDefEq.respectTransparency false in
/-- Effective addresses and their initialized RAM cells come from the pooled
    read/address history and actual decoder query, including cross-family reads. -/
theorem pooled_word_address {p : Nat} [Fact p.Prime]
    (hp : 536870912 ≤ p) (inverse : (-3840 : ZMod p) * 524288 = 1)
    {trace : PooledTrace p} (accepted : Accepted trace) (clocks : ClockBoundary trace)
    {initial : State} {cells : List Cell}
    (image : initialImage initial cells = some trace.initialMemory)
    (wordSetup : trace.rom.wordMemory = ROM.table cells trace.initialMemory)
    {values : Nat → BitVec 32} (subwordSetup : trace.rom.subwordMemory = Verification.subwordTable values)
    {addresses : List (BitVec 32)} {program : List PooledProgramEntry}
    (programImage : pooledProgramImage initial addresses = some program)
    (decoded : PooledDecoded trace program)
    {w : Nat → ZMod p} (member : (⟨.wordMemory, w⟩ : Row p PooledFamily) ∈ trace.rows)
    {entry : PooledProgramEntry} (present : entry ∈ program)
    (family : entry.data.family = .wordMemory)
    (query : (⟨.wordMemory, w⟩ : Row p PooledFamily).decoderQuery = entry.query)
    (store : Bool) (selected : w 10 = if store then 1 else 0) :
    let address := Word.mk (w (if store then 25 else 19)).val (w (if store then 26 else 20)).val
    address.Bounded ∧ address.toBitVec = (Word.mk (w 17).val (w 18).val).toBitVec +
      (Word.mk (w 8).val (w 9).val).toBitVec ∧ Cell.ram address.toBitVec ∈ cells := by
  have clockSize : 2 * timestampBase + 4 < p := by dsimp [timestampBase]; omega
  have limbSize : limbBase < p := by dsimp [limbBase]; omega
  have oneValue : (1 : ZMod p).val = 1 := by
    simpa only [Nat.cast_one] using ZMod.val_natCast_of_lt (by omega : 1 < p)
  have source := (pooled_value_bounds (by omega) inverse accepted clocks image wordSetup subwordSetup
    programImage decoded).1 _ member WordMemory.importedConstraintsMemoryPorts[0]
    (by change WordMemory.importedConstraintsMemoryPorts[0] ∈ WordMemory.importedConstraintsMemoryPorts
        simp [WordMemory.importedConstraintsMemoryPorts])
  have sourceBound : (Word.mk (w 17).val (w 18).val).Bounded := by
    simpa [read_word, WordMemory.importedConstraintsMemoryPorts] using source
  have fetched := run_program_sources programImage entry present
  have immediateBound : (Word.mk (w 8).val (w 9).val).Bounded := by
    obtain original | original | original | original | original := pooled_source_cases fetched
    all_goals obtain ⟨originalEntry, originalSource, equal⟩ := original
    all_goals subst entry
    · rw [mapped_query] at query
      change (⟨.wordMemory, w⟩ : Row p).decoderQuery = originalEntry.query at query
      exact query_immediate limbSize (row := (⟨.wordMemory, w⟩ : Row p)) originalSource.fields query
    · simp [ProgramEntry.mapFamily, DecoderData.mapFamily] at family
    · simp [ProgramEntry.mapFamily, DecoderData.mapFamily] at family
    · simp [ProgramEntry.mapFamily, DecoderData.mapFamily] at family
    · simp [ProgramEntry.mapFamily, DecoderData.mapFamily] at family
  have core := Verification.holds_of_sublist (accepted.constraints _ member)
    (List.sublist_append_left (WordMemory.importedConstraints trace.rom.wordMemory)
      WordMemory.importedConstraintsTimestampLookups)
  cases store
  all_goals dsimp only [Bool.false_eq_true, if_false, if_true] at selected ⊢
  · have portMember : WordMemory.importedConstraintsMemoryPorts[1] ∈
        (⟨.wordMemory, w⟩ : Row p PooledFamily).ports := by
      change WordMemory.importedConstraintsMemoryPorts[1] ∈ WordMemory.importedConstraintsMemoryPorts
      simp [WordMemory.importedConstraintsMemoryPorts]
    have bound := address_bounds clockSize inverse accepted clocks image _ member _ portMember
    have cell := row_ram_cell clockSize inverse accepted clocks image member portMember
      (by refine ⟨Nat.pair (w 19).val (w 20).val, ?_⟩
          simp [WordMemory.importedConstraintsMemoryPorts, MemoryAddress.code, selected, pairCode, oneValue])
    exact local_word_address (by dsimp [ROM.limit]; omega) inverse core false selected
      sourceBound immediateBound bound cell.1
  · have portMember : WordMemory.importedConstraintsMemoryPorts[2] ∈
        (⟨.wordMemory, w⟩ : Row p PooledFamily).ports := by
      change WordMemory.importedConstraintsMemoryPorts[2] ∈ WordMemory.importedConstraintsMemoryPorts
      simp [WordMemory.importedConstraintsMemoryPorts]
    have bound := address_bounds clockSize inverse accepted clocks image _ member _ portMember
    have cell := row_ram_cell clockSize inverse accepted clocks image member portMember
      (by refine ⟨Nat.pair (w 25).val (w 26).val, ?_⟩
          simp [WordMemory.importedConstraintsMemoryPorts, MemoryAddress.code, selected, pairCode, oneValue])
    exact local_word_address (by dsimp [ROM.limit]; omega) inverse core true selected
      sourceBound immediateBound bound cell.1

set_option backward.isDefEq.respectTransparency false in
/-- The same pooled grouped history realizes actual Sail word-RAM accesses.
    Canonical addresses are recovered from initialized cells, not assumed. -/
theorem pooled_word_native_transport {p : Nat} [Fact p.Prime]
    (hp : 33554432 < p) (inverse : (-3840 : ZMod p) * 524288 = 1)
    {trace : PooledTrace p} (accepted : Accepted trace) (clocks : ClockBoundary trace)
    {initial : State} {cells : List Cell}
    (image : initialImage initial cells = some trace.initialMemory)
    {w : Nat → ZMod p} (member : (⟨.wordMemory, w⟩ : Row p PooledFamily) ∈ trace.rows)
    (store : Bool) (selected : w 10 = if store then 1 else 0)
    {before after : State}
    (history : SailHistory cells
      (rowEvents trace.memoryEpoch (⟨.wordMemory, w⟩ : Row p PooledFamily)).reverse before after) :
    if store then
      run (writeMemory (size := 4) (Word.mk (w 25).val (w 26).val).toBitVec
        (Word.mk (w 31).val (w 32).val).toBitVec) before = .ok () after
    else
      (_root_.Sail.ArchSem.readBytes (ue := SailRV32.exception) 4
        (Word.mk (w 19).val (w 20).val).toBitVec.toNat).run before =
        .ok (Word.mk (w 23).val (w 24).val).toBitVec before := by
  have clockSize : 2 * timestampBase + 4 < p := by dsimp [timestampBase]; omega
  have oneValue : (1 : ZMod p).val = 1 := by
    simpa only [Nat.cast_one] using ZMod.val_natCast_of_lt (by omega : 1 < p)
  cases store
  · simp only [Bool.false_eq_true, if_false] at selected ⊢
    have present : WordMemory.importedConstraintsMemoryPorts[1] ∈
        (⟨.wordMemory, w⟩ : Row p PooledFamily).ports := by
      change WordMemory.importedConstraintsMemoryPorts[1] ∈ WordMemory.importedConstraintsMemoryPorts
      simp [WordMemory.importedConstraintsMemoryPorts]
    have cell := row_ram_cell clockSize inverse accepted clocks image member present
      (by refine ⟨Nat.pair (w 19).val (w 20).val, ?_⟩
          simp [WordMemory.importedConstraintsMemoryPorts, MemoryAddress.code, selected, pairCode, oneValue])
    have read := native_history_read trace.memoryEpoch rfl rfl rfl history present cell.2
    simpa [WordMemory.importedConstraintsMemoryPorts, MemoryPort.readCode, pairCode, memoryWord, MemoryAddress.word, Cell.read] using read
  · simp only [if_true] at selected ⊢
    have present : WordMemory.importedConstraintsMemoryPorts[2] ∈
        (⟨.wordMemory, w⟩ : Row p PooledFamily).ports := by
      change WordMemory.importedConstraintsMemoryPorts[2] ∈ WordMemory.importedConstraintsMemoryPorts
      simp [WordMemory.importedConstraintsMemoryPorts]
    have cell := row_ram_cell clockSize inverse accepted clocks image member present
      (by refine ⟨Nat.pair (w 25).val (w 26).val, ?_⟩
          simp [WordMemory.importedConstraintsMemoryPorts, MemoryAddress.code, selected, pairCode, oneValue])
    have written := native_history_write trace.memoryEpoch rfl rfl rfl history rfl cell.2
    simpa [WordMemory.importedConstraintsMemoryPorts, MemoryPort.writeCode, pairCode, memoryWord, MemoryAddress.word, Cell.write] using written

end Airbender.Trace.Proofs
