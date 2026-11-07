import Human.Trace.Families.ShiftBinop.RVTheorems
import Slop.ShiftBinop.RVTraceSoundness
import Slop.ShiftBinop.RVValues
import Slop.Trace.RVFamilyTrace
import Slop.Trace.RVZeroRows
import Slop.ISA.RV.DecodeShape

/-! The shift/binop trace claim on the RV route (`RVTraceSoundnessClaim`): no Sail state, interpreter or `Configured`
    fact. Each row is one `RV.exec` of its entry's instruction (`rv_row_step`: the instruction is `rvInstruction` of
    an RV input (`rv_fields_input`, immediates from `RV.decode_shape`), decoder facts `rv_query_facts`, operand
    registers and destination update from the row's RV history `rv_register_ports`, result `rv_row_value`, PC
    `pc_successor`); x0 is preserved (`shiftBinop_row_zero_preserving`) and read as zero; the composition is
    `rv_family_realizes`. -/

namespace Airbender.ShiftBinop.Proofs
open Arithmetic Trace Trace.Proofs

private theorem low_five (sh : BitVec 5) : ((sh.setWidth 12).extractLsb' 0 5).setWidth 32 = sh.setWidth 32 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.extractLsb'_toNat]
  have := sh.isLt
  omega

/-- A successful projection of a decoded instruction is the data of an RV input of this family. -/
theorem rv_fields_input {bits : RV.Word} {i : RV.Instr} {d : DecoderData Unit}
    (decodes : RV.decode bits = some i) (fields : rvDecoderFields i = some d) (s : RV.State) :
    ∃ input : RVInput, input.before = s ∧ i = rvInstruction input ∧ d = rvData input := by
  have shape := RV.decode_shape decodes
  suffices h : ∃ input : RVInput, input.before = s ∧ i = rvInstruction input by
    obtain ⟨input, hb, rfl⟩ := h
    exact ⟨input, hb, rfl, rv_fields fields⟩
  have binary {o : RV.Op} {rd rs1 : RV.Reg} {imm : RV.Word} (shape : RV.Shape (.opImm o rd rs1 imm))
      (kind : o = .xor ∨ o = .or ∨ o = .and) : ∃ x : BitVec 12, imm = x.signExtend 32 := by
    simp only [RV.Shape] at shape
    rcases shape with ⟨_, x, hx⟩ | ⟨shift, _⟩
    · exact ⟨x, hx⟩
    · rcases kind with rfl | rfl | rfl <;> simp at shift
  have shift {o : RV.Op} {rd rs1 : RV.Reg} {imm : RV.Word} (shape : RV.Shape (.opImm o rd rs1 imm))
      (kind : o = .sll ∨ o = .srl ∨ o = .sra) : ∃ x : BitVec 12, imm = (x.extractLsb' 0 5).zeroExtend 32 := by
    simp only [RV.Shape] at shape
    rcases shape with ⟨binary, _⟩ | ⟨_, sh, hsh⟩
    · rcases kind with rfl | rfl | rfl <;> simp at binary
    · exact ⟨sh.setWidth 12, by rw [hsh]; exact (low_five sh).symm⟩
  unfold rvDecoderFields at fields
  split at fields
  case h_1 rd rs1 rs2 => exact ⟨⟨.xor, false, 0, 0, ⟨0, 0⟩, rs1, rs2, rd, 0, s⟩, rfl, rfl⟩
  case h_2 rd rs1 rs2 => exact ⟨⟨.or, false, 0, 0, ⟨0, 0⟩, rs1, rs2, rd, 0, s⟩, rfl, rfl⟩
  case h_3 rd rs1 rs2 => exact ⟨⟨.and, false, 0, 0, ⟨0, 0⟩, rs1, rs2, rd, 0, s⟩, rfl, rfl⟩
  case h_4 rd rs1 rs2 => exact ⟨⟨.sll, false, 0, 0, ⟨0, 0⟩, rs1, rs2, rd, 0, s⟩, rfl, rfl⟩
  case h_5 rd rs1 rs2 => exact ⟨⟨.srl, false, 0, 0, ⟨0, 0⟩, rs1, rs2, rd, 0, s⟩, rfl, rfl⟩
  case h_6 rd rs1 rs2 => exact ⟨⟨.sra, false, 0, 0, ⟨0, 0⟩, rs1, rs2, rd, 0, s⟩, rfl, rfl⟩
  case h_7 rd rs1 imm =>
    obtain ⟨x, rfl⟩ := binary shape (by simp)
    exact ⟨⟨.xor, true, 0, 0, ⟨0, 0⟩, rs1, 0, rd, x, s⟩, rfl, rfl⟩
  case h_8 rd rs1 imm =>
    obtain ⟨x, rfl⟩ := binary shape (by simp)
    exact ⟨⟨.or, true, 0, 0, ⟨0, 0⟩, rs1, 0, rd, x, s⟩, rfl, rfl⟩
  case h_9 rd rs1 imm =>
    obtain ⟨x, rfl⟩ := binary shape (by simp)
    exact ⟨⟨.and, true, 0, 0, ⟨0, 0⟩, rs1, 0, rd, x, s⟩, rfl, rfl⟩
  case h_10 rd rs1 imm =>
    obtain ⟨x, rfl⟩ := shift shape (by simp)
    exact ⟨⟨.sll, true, 0, 0, ⟨0, 0⟩, rs1, 0, rd, x, s⟩, rfl, rfl⟩
  case h_11 rd rs1 imm =>
    obtain ⟨x, rfl⟩ := shift shape (by simp)
    exact ⟨⟨.srl, true, 0, 0, ⟨0, 0⟩, rs1, 0, rd, x, s⟩, rfl, rfl⟩
  case h_12 rd rs1 imm =>
    obtain ⟨x, rfl⟩ := shift shape (by simp)
    exact ⟨⟨.sra, true, 0, 0, ⟨0, 0⟩, rs1, 0, rd, x, s⟩, rfl, rfl⟩
  case h_13 rd rs1 => exact ⟨⟨.rev8, false, 0, 0, ⟨0, 0⟩, rs1, 0, rd, 0, s⟩, rfl, rfl⟩
  case h_14 => cases fields

/-- Every row of an accepted RV-decoded trace preserves x0. -/
theorem rv_zero_preserving {p : Nat} [Fact p.Prime] (hp : limbBase < p)
    {trace : NativeTrace p} {initial : RV.State} {addresses : List (BitVec 32)} {program : List RVProgramEntry}
    (image : rvProgramImageWith rvDecoderFields initial addresses = some program)
    (decoded : RVDecoded trace program) : ZeroPreserving trace := by
  intro row member
  obtain ⟨entry, present, _, query⟩ := rv_decoder_member (decoded row member)
  obtain ⟨_, _, i, _, fields⟩ := rvProgram_entry_fetch image entry present
  exact RVZero.shiftBinop_row_zero_preserving hp row entry fields query

/-- One shift/binop row is one `RV.exec` of its entry's instruction, agreeing with the row's RV history and final PC.
    `zeroRead`: the second port reads zero when it addresses x0 (the trace's x0 law). -/
theorem rv_row_step {p : Nat} [Fact p.Prime] (hp : 536870912 ≤ p) (inverse : (-30720 : ZMod p) * 65536 = 1)
    {w : Nat → ZMod p}
    (core : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    {entry : RVProgramEntry} (query : decoderQuery w = entry.query)
    {i : RV.Instr} (decodes : RV.decode entry.bits = some i) (fields : rvDecoderFields i = some entry.data)
    (zeroRead : w 6 = 0 → importedConstraintsMemoryPorts[1].readCode w = 0)
    {cells : List Cell} (epoch : Nat) {before after : RV.State} (pc : before.pc = entry.pc)
    (history : RVHistory cells (rowEvents epoch (⟨.shiftBinop, w⟩ : Row p TraceKind)).reverse before after) :
    ∃ next, RV.exec before i = some next ∧
      RV.Same next { after with pc := (⟨.shiftBinop, w⟩ : Row p TraceKind).finish.word.toBitVec } := by
  obtain ⟨input, rfl, rfl, data⟩ := rv_fields_input decodes fields before
  let pooled : RVPooledProgramEntry := entry.mapFamily (fun _ => .shiftBinop)
  have pooledData : pooled.data = (rvData input).mapFamily (fun _ => .shiftBinop) := by
    simp only [pooled, RVProgramEntry.mapFamily, data]
  obtain ⟨selected, funct3, immediateLo, immediateHi, pcWord, rs1Query, rs2Query, rdQuery⟩ :=
    rv_query_facts hp core pooledData (p := p) (w := w) query
  change _ = Word.ofBitVec entry.pc at pcWord
  -- Operand registers and destination update, from the row's RV history.
  have index {column : Nat} {k : BitVec 5} (equal : w column = (k.toNat : ZMod p)) :
      (w column).val = k.toNat := by
    rw [equal, ZMod.val_natCast, Nat.mod_eq_of_lt (by have := k.isLt; omega)]
  have shaped : RVHistory cells (nativeRowEvents epoch importedConstraintsTraceColumns
      #[importedConstraintsMemoryPorts[0], importedConstraintsMemoryPorts[1], importedConstraintsMemoryPorts[2]]
      w).reverse input.before after := history
  obtain ⟨left, right, written⟩ := rv_register_ports epoch (by simp [importedConstraintsMemoryPorts])
    (by simp [importedConstraintsMemoryPorts]) (a := 5) (b := 6) (c := 7)
    (by simp [importedConstraintsMemoryPorts]) (by simp [importedConstraintsMemoryPorts])
    (by simp [importedConstraintsMemoryPorts]) (index rs1Query) (index rs2Query) (index rdQuery) shaped
  have destinationWord : memoryWord ((importedConstraintsMemoryPorts[2]).writeCode w) =
      (Word.mk (w 31).val (w 32).val).toBitVec := by
    simp [importedConstraintsMemoryPorts, MemoryPort.writeCode, pairCode, memoryWord]
  rw [destinationWord] at written
  -- The row calculation and the PC.
  have ignoredZero : (input.immediate || input.operation = .rev8) = true →
      importedConstraintsMemoryPorts[1].readCode w = 0 := by
    intro ignored
    exact zeroRead (by simpa [ignored] using rs2Query)
  have result := rv_row_value (by omega) core input.operation input.immediate input.encodedImmediate
    selected funct3 immediateLo immediateHi ignoredZero
  have value : rvValue input.operation input.immediate input.encodedImmediate
      (input.before.getReg input.rs1) (input.before.getReg input.rs2) = (Word.mk (w 31).val (w 32).val).toBitVec := by
    rw [result, left, ← right]
    by_cases ignored : (input.immediate || input.operation = .rev8) = true
    · exact rv_value_second _ _ _ _ ignored
    · split
      · contradiction
      · rfl
  have pcBound : (Word.mk (w 0).val (w 1).val).Bounded := by
    rw [pcWord]; exact Word.ofBitVec_bound entry.pc
  have pcNext := pc_successor (by omega) inverse core (initial := Word.mk (w 0).val (w 1).val)
    (final := Word.mk (w 13).val (w 14).val)
    ⟨(ZMod.natCast_zmod_val _).symm, (ZMod.natCast_zmod_val _).symm, rfl, rfl⟩ pcBound
  have finalPC : (⟨.shiftBinop, w⟩ : Row p TraceKind).finish.word.toBitVec = input.before.pc + 4 := by
    change (Word.mk (w 13).val (w 14).val).toBitVec = _
    rw [pcNext.2.2, pcWord, Word.ofBitVec_roundtrip, pc]
  refine ⟨_, rv_exec_row _ _, rv_same_next ?_ finalPC⟩
  rw [value]
  exact written

/-- `ShiftBinop.RVTraceSoundnessClaim`, proved. -/
theorem rv_trace_execution {p : Nat} [Fact p.Prime]
    (hp : 536870912 ≤ p) (inverse : (-30720 : ZMod p) * 65536 = 1)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    {trace : NativeTrace p} {initial : RV.State} {cells : List Cell} {program : List RVProgramEntry}
    (inputs : RVExecutionInputs trace initial cells program)
    (accepted : Accepted trace) (decoded : RVDecoded trace program) :
    RVRealizes trace initial cells := by
  have clockSize : 2 * timestampBase + 4 < p := by dsimp [timestampBase]; omega
  have limbSize : limbBase < p := by dsimp [limbBase]; omega
  obtain ⟨addresses, image⟩ := inputs.programImage
  have zero := rv_zero_preserving limbSize image decoded
  have zeroReads := RVZero.rv_zero_reads_of_preserving clockSize clockInverse accepted inputs.clocks
    inputs.image zero
  refine rv_family_realizes clockSize clockInverse accepted inputs zero
    (rv_family_row_steps limbSize image (fun _ _ => True)
      (fun row member => by
        obtain ⟨entry, present, _, query⟩ := rv_decoder_member (decoded row member)
        exact ⟨entry, present, trivial, query⟩) ?_)
  intro row member entry _ _ query i decodes fields _ before after pc _ history
  obtain ⟨family, w⟩ := row
  cases family
  have core := Verification.holds_of_sublist (accepted.constraints _ member)
    (List.sublist_append_left importedConstraints importedConstraintsTimestampLookups)
  have zeroRead (atZero : w 6 = 0) : importedConstraintsMemoryPorts[1].readCode w = 0 := by
    have present : importedConstraintsMemoryPorts[1] ∈ (⟨.shiftBinop, w⟩ : Row p TraceKind).ports := by
      change importedConstraintsMemoryPorts[1] ∈ importedConstraintsMemoryPorts
      simp [importedConstraintsMemoryPorts]
    exact zeroReads _ member _ present
      (by simp [importedConstraintsMemoryPorts, MemoryAddress.code, Cell.addressCode, atZero])
  exact rv_row_step hp inverse core query decodes fields zeroRead trace.memoryEpoch pc history

end Airbender.ShiftBinop.Proofs
