import Airbender.Proofs.Trace.PooledHistory
import Airbender.Proofs.MulDiv.Composition
import Airbender.Proofs.ShiftBinop.Composition

namespace Airbender.Trace.Proofs
open Arithmetic Reference.RiscV.Sail Reference.Sail
open _root_.Sail.ArchSem
variable [MemoryPlatform SailRV32.exception]

set_option backward.isDefEq.respectTransparency false in
/-- Original multiply/divide clauses consume the shared mixed-family history
    and its derived input bounds. No separate family history is supplied. -/
theorem pooled_muldiv_execution {p : Nat} [Fact p.Prime]
    (hp : 536870912 ≤ p) (inverse : (-3840 : ZMod p) * 524288 = 1)
    {trace : PooledTrace p} (accepted : Accepted trace) (clocks : ClockBoundary trace)
    {initial : State} {cells : List Cell}
    (image : initialImage initial cells = some trace.initialMemory)
    (wordSetup : trace.rom.wordMemory = ROM.table cells trace.initialMemory)
    {values : Nat → BitVec 32} (subwordSetup : trace.rom.subwordMemory = Verification.subwordTable values)
    {addresses : List (BitVec 32)} {program : List PooledProgramEntry}
    (programImage : pooledProgramImage initial addresses = some program)
    (decoded : PooledDecoded trace program)
    {w : Nat → ZMod p} (member : (⟨.mulDiv, w⟩ : Row p PooledFamily) ∈ trace.rows)
    {entry : PooledProgramEntry} (present : entry ∈ program)
    (family : entry.data.family = .mulDiv) (query : MulDiv.decoderQuery w = entry.query)
    {before after : State}
    (history : SailHistory cells (MulDiv.Proofs.nativeEvents trace.memoryEpoch w).reverse before after) :
    ∃ clause, instructionClause entry.instruction = some clause ∧
      run (normalStep clause) (retiredState before (Word.mk (w 0).val (w 1).val).toBitVec) =
        .ok SailRV32.Functions.RETIRE_SUCCESS
          (retiredState after (Word.mk (w 14).val (w 15).val).toBitVec) := by
  have core := Verification.holds_of_sublist (accepted.constraints _ member)
    (List.sublist_append_left MulDiv.importedConstraints MulDiv.importedConstraintsTimestampLookups)
  have bound := (pooled_value_bounds (by omega) inverse accepted clocks image wordSetup subwordSetup
    programImage decoded).1 _ member MulDiv.importedConstraintsMemoryPorts[0]
      (by change MulDiv.importedConstraintsMemoryPorts[0] ∈ MulDiv.importedConstraintsMemoryPorts; simp [MulDiv.importedConstraintsMemoryPorts])
  have left : (Word.mk (w 20).val (w 21).val).Bounded := by
    simpa [read_word, MulDiv.importedConstraintsMemoryPorts] using bound
  have source := run_program_sources programImage entry present
  obtain original | original | original | original | original := pooled_source_cases source
  all_goals obtain ⟨originalEntry, originalSource, equal⟩ := original
  all_goals subst entry
  · cases mode : originalEntry.data.family <;>
      simp [ProgramEntry.mapFamily, DecoderData.mapFamily, mode, pooledArithmeticFamily] at family
  · simp [ProgramEntry.mapFamily, DecoderData.mapFamily] at family
  · rw [mapped_query] at query
    have arithmeticInverse : (-30720 : ZMod p) * 65536 = 1 := by
      calc
        (-30720 : ZMod p) * 65536 = (-3840 : ZMod p) * 524288 := by ring
        _ = 1 := inverse
    exact MulDiv.Proofs.local_instruction_execution hp arithmeticInverse core trace.memoryEpoch
      originalSource query left history
  · simp [ProgramEntry.mapFamily, DecoderData.mapFamily] at family
  · simp [ProgramEntry.mapFamily, DecoderData.mapFamily] at family

set_option backward.isDefEq.respectTransparency false in
/-- Shift/binop/REV8 clauses use exact x0 reads proved through the pooled
    history. Imported byte/assembly relations derive their remaining interfaces. -/
theorem pooled_shift_execution {p : Nat} [Fact p.Prime]
    (hp : 536870912 ≤ p) (inverse : (-3840 : ZMod p) * 524288 = 1)
    {trace : PooledTrace p} (accepted : Accepted trace) (clocks : ClockBoundary trace)
    {initial : State} {cells : List Cell}
    (image : initialImage initial cells = some trace.initialMemory)
    {addresses : List (BitVec 32)} {program : List PooledProgramEntry}
    (programImage : pooledProgramImage initial addresses = some program)
    (decoded : PooledDecoded trace program)
    {w : Nat → ZMod p} (member : (⟨.shiftBinop, w⟩ : Row p PooledFamily) ∈ trace.rows)
    {entry : PooledProgramEntry} (present : entry ∈ program)
    (family : entry.data.family = .shiftBinop) (query : ShiftBinop.decoderQuery w = entry.query)
    {before after : State}
    (history : SailHistory cells (ShiftBinop.Proofs.nativeEvents trace.memoryEpoch w).reverse before after) :
    ∃ clause, instructionClause entry.instruction = some clause ∧
      run (normalStep clause) (retiredState before (Word.mk (w 0).val (w 1).val).toBitVec) =
        .ok SailRV32.Functions.RETIRE_SUCCESS
          (retiredState after (Word.mk (w 13).val (w 14).val).toBitVec) := by
  have core := Verification.holds_of_sublist (accepted.constraints _ member)
    (List.sublist_append_left ShiftBinop.importedConstraints ShiftBinop.importedConstraintsTimestampLookups)
  have clockField : 2 * timestampBase + 4 < p := by dsimp [timestampBase]; omega
  have preserves := pooled_zero_preserving (by omega) accepted programImage decoded
  have zeros : ∀ port ∈ ShiftBinop.importedConstraintsMemoryPorts,
      port.address.code w = (Cell.register 0).addressCode → (readToken w port).value = 0 := by
    intro port present atZero
    exact zero_reads_of_preserving clockField inverse accepted clocks image preserves
      _ member port (by change port ∈ ShiftBinop.importedConstraintsMemoryPorts; exact present) atZero
  have source := run_program_sources programImage entry present
  obtain original | original | original | original | original := pooled_source_cases source
  all_goals obtain ⟨originalEntry, originalSource, equal⟩ := original
  all_goals subst entry
  · cases mode : originalEntry.data.family <;>
      simp [ProgramEntry.mapFamily, DecoderData.mapFamily, mode, pooledArithmeticFamily] at family
  · simp [ProgramEntry.mapFamily, DecoderData.mapFamily] at family
  · simp [ProgramEntry.mapFamily, DecoderData.mapFamily] at family
  · rw [mapped_query] at query
    have arithmeticInverse : (-30720 : ZMod p) * 65536 = 1 := by
      calc
        (-30720 : ZMod p) * 65536 = (-3840 : ZMod p) * 524288 := by ring
        _ = 1 := inverse
    exact ShiftBinop.Proofs.local_instruction_execution hp arithmeticInverse core (accepted.active _ member)
      trace.memoryEpoch originalSource query zeros history
  · simp [ProgramEntry.mapFamily, DecoderData.mapFamily] at family

end Airbender.Trace.Proofs
