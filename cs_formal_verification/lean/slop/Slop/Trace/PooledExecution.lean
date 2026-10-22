import Slop.JumpBranchSlt.Composition
import Slop.Trace.PooledPC
import Slop.Trace.Arithmetic
import Slop.Trace.PooledHistory
import Slop.MulDiv.Composition
import Slop.ShiftBinop.Composition

namespace Airbender.Trace.Proofs
open Arithmetic Reference.RiscV.Sail Reference.Sail
open _root_.Sail.ArchSem

set_option backward.isDefEq.respectTransparency false in
/-- Original multiply/divide clauses consume the shared mixed-family history
    and its derived input bounds. No separate family history is supplied. -/
theorem pooled_muldiv_execution {p : Nat} [Fact p.Prime]
    {projection : SailRV32.instruction → Option (DecoderData PooledFamily)}
    [registry : PooledRegistry projection]
    (hp : 536870912 ≤ p) (inverse : (-3840 : ZMod p) * 524288 = 1)
    {trace : PooledTrace p} (accepted : Accepted trace) (clocks : ClockBoundary trace)
    {initial : State} {cells : List Cell}
    (image : initialImage initial cells = some trace.initialMemory)
    (wordSetup : trace.rom.wordMemory = ROM.table cells trace.initialMemory)
    {values : Nat → BitVec 32} (subwordSetup : trace.rom.subwordMemory = Verification.subwordTable values)
    {addresses : List (BitVec 32)} {program : List PooledProgramEntry}
    (programImage : programImageRunWith projection initial addresses = some program)
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
  obtain original | original | original | original | original := registry.sourceCases source
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
    {projection : SailRV32.instruction → Option (DecoderData PooledFamily)}
    [registry : PooledRegistry projection]
    (hp : 536870912 ≤ p) (inverse : (-3840 : ZMod p) * 524288 = 1)
    {trace : PooledTrace p} (accepted : Accepted trace) (clocks : ClockBoundary trace)
    {initial : State} {cells : List Cell}
    (image : initialImage initial cells = some trace.initialMemory)
    {addresses : List (BitVec 32)} {program : List PooledProgramEntry}
    (programImage : programImageRunWith projection initial addresses = some program)
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
  obtain original | original | original | original | original := registry.sourceCases source
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

set_option maxHeartbeats 2000000 in
set_option backward.isDefEq.respectTransparency false in
/-- Arithmetic retirement uses both operands from the same pooled history.
    Original Sail decoding fixes the immediate and preprocessing. -/
theorem pooled_arithmetic_execution {p : Nat} [Fact p.Prime]
    (profile : ISAProfile) (hp : 536870912 ≤ p) (inverse : (-3840 : ZMod p) * 524288 = 1)
    {trace : PooledTrace p} (accepted : Accepted trace) (clocks : ClockBoundary trace)
    {initial : State} {cells : List Cell}
    (image : initialImage initial cells = some trace.initialMemory)
    (wordSetup : trace.rom.wordMemory = ROM.table cells trace.initialMemory)
    {values : Nat → BitVec 32} (subwordSetup : trace.rom.subwordMemory = Verification.subwordTable values)
    (registers : ∀ index, Cell.register index ∈ cells)
    {addresses : List (BitVec 32)} {program : List PooledProgramEntry}
    (programImage : pooledProgramImage initial addresses = some program)
    (decoded : PooledDecoded trace program)
    {w : Nat → ZMod p} (member : (⟨.addSub, w⟩ : Row p PooledFamily) ∈ trace.rows)
    {entry : PooledProgramEntry} (present : entry ∈ program)
    (family : entry.data.family = .addSub)
    (query : (⟨.addSub, w⟩ : Row p PooledFamily).decoderQuery = entry.query)
    (loads : profile = .sail → ∀ (imm : BitVec 12) (rs1 : BitVec 5),
      entry.instruction ≠ .LOAD (imm, .Regidx rs1, .Regidx 0, false, 4))
    {before after : State} {events : List MemoryAccess}
    (past : SailHistory cells events initial before)
    (history : SailHistory cells (rowEvents trace.memoryEpoch (⟨.addSub, w⟩ : Row p PooledFamily)).reverse before after) :
    ∃ clause, profileClause profile entry.instruction = some clause ∧
      run (normalStep clause) (retiredState before (Word.mk (w 0).val (w 1).val).toBitVec) =
        .ok SailRV32.Functions.RETIRE_SUCCESS
          (retiredState after (Word.mk (w 19).val (w 20).val).toBitVec) := by
  have field : limbBase < p := by dsimp [limbBase, ROM.limit] at *; omega
  have bounds := (pooled_value_bounds (by omega) inverse
    accepted clocks image wordSetup subwordSetup programImage decoded).1 _ member
  have left := bounds AddSub.importedConstraintsMemoryPorts[0]
    (by change AddSub.importedConstraintsMemoryPorts[0] ∈ AddSub.importedConstraintsMemoryPorts
        simp [AddSub.importedConstraintsMemoryPorts])
  have right := bounds AddSub.importedConstraintsMemoryPorts[1]
    (by change AddSub.importedConstraintsMemoryPorts[1] ∈ AddSub.importedConstraintsMemoryPorts
        simp [AddSub.importedConstraintsMemoryPorts])
  have readBounds : (Word.mk (w 25).val (w 26).val).Bounded ∧
      (Word.mk (w 29).val (w 30).val).Bounded := by
    simpa [read_word, AddSub.importedConstraintsMemoryPorts] using And.intro left right
  have source := run_program_sources programImage entry present
  obtain original | original | original | original | original := pooled_source_cases source
  all_goals obtain ⟨originalEntry, originalSource, equal⟩ := original
  all_goals subst entry
  · rw [mapped_query] at query
    change (⟨.addSub, w⟩ : Row p).decoderQuery = originalEntry.query at query
    have localFamily : originalEntry.data.family = .addSub := by
      cases mode : originalEntry.data.family
      · rfl
      · simp [ProgramEntry.mapFamily, DecoderData.mapFamily, mode, pooledArithmeticFamily] at family
    exact local_arithmetic_instruction_execution profile (by dsimp [ROM.limit]; omega) inverse image trace.rom.wordMemory
      trace.memoryEpoch registers (accepted.constraints _ member) (accepted.active _ member)
      ⟨readBounds.1, readBounds.2, query_immediate field (row := (⟨.addSub, w⟩ : Row p)) originalSource.fields query⟩
      originalSource.fields localFamily query loads past history
  · simp [ProgramEntry.mapFamily, DecoderData.mapFamily] at family
  · simp [ProgramEntry.mapFamily, DecoderData.mapFamily] at family
  · simp [ProgramEntry.mapFamily, DecoderData.mapFamily] at family
  · simp [ProgramEntry.mapFamily, DecoderData.mapFamily] at family

theorem pooled_control_bounds {p : Nat} [Fact p.Prime]
    {projection : SailRV32.instruction → Option (DecoderData PooledFamily)}
    [registry : PooledRegistry projection]
    (hp : 536870912 ≤ p) (inverse : (-3840 : ZMod p) * 524288 = 1)
    {trace : PooledTrace p} (accepted : Accepted trace) (clocks : ClockBoundary trace)
    {initial : State} {cells : List Cell}
    (image : initialImage initial cells = some trace.initialMemory)
    (wordSetup : trace.rom.wordMemory = ROM.table cells trace.initialMemory)
    {values : Nat → BitVec 32} (subwordSetup : trace.rom.subwordMemory = Verification.subwordTable values)
    {addresses : List (BitVec 32)} {program : List PooledProgramEntry}
    (programImage : programImageRunWith projection initial addresses = some program)
    (decoded : PooledDecoded trace program)
    (code : ∀ entry ∈ program, entry.pc.toNat % 4 = 0)
    (terminal : trace.terminal.word.Bounded)
    {w : Nat → ZMod p} (member : (⟨.jumpBranchSlt, w⟩ : Row p PooledFamily) ∈ trace.rows) :
    (Word.mk (w 22).val (w 23).val).Bounded ∧
      (Word.mk (w 26).val (w 27).val).Bounded ∧
      (w 0).val % 4 = 0 ∧ (w 17).val < limbBase := by
  have field : limbBase < p := by dsimp [limbBase]; omega
  have bounds := (pooled_value_bounds (by omega) inverse accepted clocks image wordSetup subwordSetup
    programImage decoded).1 _ member
  have left := bounds JumpBranchSlt.importedConstraintsMemoryPorts[0]
    (by change JumpBranchSlt.importedConstraintsMemoryPorts[0] ∈ JumpBranchSlt.importedConstraintsMemoryPorts
        simp [JumpBranchSlt.importedConstraintsMemoryPorts])
  have right := bounds JumpBranchSlt.importedConstraintsMemoryPorts[1]
    (by change JumpBranchSlt.importedConstraintsMemoryPorts[1] ∈ JumpBranchSlt.importedConstraintsMemoryPorts
        simp [JumpBranchSlt.importedConstraintsMemoryPorts])
  have readBounds : (Word.mk (w 22).val (w 23).val).Bounded ∧
      (Word.mk (w 26).val (w 27).val).Bounded := by
    simpa [read_word, JumpBranchSlt.importedConstraintsMemoryPorts] using And.intro left right
  have finalHi := ((pooled_pc_bounds field accepted decoded terminal) _ member).2.2
  have aligned := pooled_pc_alignment field decoded code _ member
  exact ⟨readBounds.1, readBounds.2, aligned, finalHi⟩

set_option backward.isDefEq.respectTransparency false in
/-- Control-flow operands come from the same initialized pooled history.
    Decoder-bound PCs supply intermediate ranges; canonical termination stays
    explicit because the jump artifact does not enforce that endpoint. -/
theorem pooled_control_execution {p : Nat} [Fact p.Prime]
    {projection : SailRV32.instruction → Option (DecoderData PooledFamily)}
    [registry : PooledRegistry projection]
    (hp : 536870912 ≤ p) (inverse : (-3840 : ZMod p) * 524288 = 1)
    {trace : PooledTrace p} (accepted : Accepted trace) (clocks : ClockBoundary trace)
    {initial : State} {cells : List Cell}
    (image : initialImage initial cells = some trace.initialMemory)
    (wordSetup : trace.rom.wordMemory = ROM.table cells trace.initialMemory)
    {values : Nat → BitVec 32} (subwordSetup : trace.rom.subwordMemory = Verification.subwordTable values)
    {addresses : List (BitVec 32)} {program : List PooledProgramEntry}
    (programImage : programImageRunWith projection initial addresses = some program)
    (decoded : PooledDecoded trace program)
    (code : ∀ entry ∈ program, entry.pc.toNat % 4 = 0)
    (terminal : trace.terminal.word.Bounded)
    {w : Nat → ZMod p} (member : (⟨.jumpBranchSlt, w⟩ : Row p PooledFamily) ∈ trace.rows)
    {entry : PooledProgramEntry} (present : entry ∈ program)
    (family : entry.data.family = .jumpBranchSlt) (query : JumpBranchSlt.decoderQuery w = entry.query)
    {before after : State} {events : List MemoryAccess}
    (past : SailHistory cells events initial before)
    (history : SailHistory cells (JumpBranchSlt.Proofs.nativeEvents trace.memoryEpoch w).reverse before after)
    (isa : ∃ value, initial.regs.get? .misa = some value)
    (configuration : initial.regs.get? .cur_privilege = some .Machine ∧
      ∃ security, initial.regs.get? .mseccfg = some security ∧
        SailRV32.Functions._get_Seccfg_MLPE security = 0) :
    ∃ clause, instructionClause entry.instruction = some clause ∧
      run (normalStep clause) (retiredState before (Word.mk (w 0).val (w 1).val).toBitVec) =
        .ok SailRV32.Functions.RETIRE_SUCCESS
          (retiredState after (Word.mk (w 16).val (w 17).val).toBitVec) := by
  obtain ⟨leftBound, rightBound, aligned, finalHi⟩ := pooled_control_bounds hp inverse
    accepted clocks image wordSetup subwordSetup programImage decoded code terminal member
  have core := Verification.holds_of_sublist (accepted.constraints _ member)
    (List.sublist_append_left JumpBranchSlt.importedConstraints JumpBranchSlt.importedConstraintsTimestampLookups)
  have source := run_program_sources programImage entry present
  obtain original | original | original | original | original := registry.sourceCases source
  all_goals obtain ⟨originalEntry, originalSource, equal⟩ := original
  all_goals subst entry
  · cases mode : originalEntry.data.family <;>
      simp [ProgramEntry.mapFamily, DecoderData.mapFamily, mode, pooledArithmeticFamily] at family
  · rw [mapped_query] at query
    exact JumpBranchSlt.Proofs.local_instruction_execution (by omega) core (accepted.active _ member)
      trace.memoryEpoch originalSource query leftBound rightBound aligned finalHi
      history past isa configuration
  · simp [ProgramEntry.mapFamily, DecoderData.mapFamily] at family
  · simp [ProgramEntry.mapFamily, DecoderData.mapFamily] at family
  · simp [ProgramEntry.mapFamily, DecoderData.mapFamily] at family

end Airbender.Trace.Proofs
