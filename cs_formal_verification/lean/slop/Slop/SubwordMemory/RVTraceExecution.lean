module
public import Human.Trace.Families.SubwordMemory.RVTheorems
public import Slop.SubwordMemory.RVQuery
public import Slop.SubwordMemory.RVData
public import Slop.SubwordMemory.RVWritable
public import Slop.SubwordMemory.Stores
public import Slop.SubwordMemory.Values
public import Slop.Trace.RVFamilyTrace
public import Slop.Trace.RVValues
public import Slop.Trace.RVZeroRows
public import Slop.Trace.RVWritable
public import Slop.ISA.RV.DecodeShape
public import Slop.ISA.RV.MemSubword
public import Slop.Defs.Helpers.Memory.Ports
public import Slop.Defs.Helpers.Memory.RowEvents
public import Slop.Defs.Helpers.Memory.History
public import Slop.Defs.Helpers.Core.Word

@[expose] public section

/-! The RAM subword trace claim on the RV route (`RVRamTraceSoundnessClaim`): no Sail state, interpreter,
    `Configured` or `OrdinaryWordAddress` fact. Each row is one `RV.exec` of its entry's instruction (`rv_row_step`,
    the per-row proof of `RVTraceSoundness.lean` with the row's ports read from its RV history): loads read the aligned
    RAM cell (`rv_ram_load_data`; a ROM-region cell is excluded by `ramDomain`), stores merge rs2's low bytes into the
    old word (`store_byte_encoding`) in RAM (`subword_store_ram_writable`); the destination update is the row's
    history. x0 is preserved (`subword_row_zero_preserving`); the composition is `rv_family_realizes`. -/

namespace Airbender.SubwordMemory.Proofs
open Arithmetic Trace Trace.Proofs

/-- A successful projection of a decoded instruction is the data of an RV input of this family (loads: rd ≠ x0). -/
theorem rv_fields_input {bits : RV.Word} {i : RV.Instr} {d : DecoderData Unit}
    (decodes : RV.decode bits = some i) (fields : rvDecoderFields i = some d) (s : RV.State) :
    ∃ input : RVInput, input.before = s ∧ i = rvInstruction input ∧ d = rvData input ∧
      (input.store = false → input.rd ≠ 0) := by
  have shape := RV.decode_shape decodes
  let z : Word := ⟨0, 0⟩
  cases i
  case load n sg rd rs1 imm =>
    simp only [RV.Shape] at shape
    obtain ⟨width, x, rfl⟩ := shape
    rcases width with rfl | rfl | rfl
    all_goals cases sg
    all_goals by_cases hz : rd = 0
    all_goals simp [rvDecoderFields, hz] at fields
    all_goals obtain ⟨-, rfl⟩ := fields
    · exact ⟨⟨false, true, false, z, z, z, z, z, rs1, 0, rd, x, s⟩, rfl, rfl, rfl, fun _ => hz⟩
    · exact ⟨⟨false, true, true, z, z, z, z, z, rs1, 0, rd, x, s⟩, rfl, rfl, rfl, fun _ => hz⟩
    · exact ⟨⟨false, false, false, z, z, z, z, z, rs1, 0, rd, x, s⟩, rfl, rfl, rfl, fun _ => hz⟩
    · exact ⟨⟨false, false, true, z, z, z, z, z, rs1, 0, rd, x, s⟩, rfl, rfl, rfl, fun _ => hz⟩
  case store n rs2 rs1 imm =>
    simp only [RV.Shape] at shape
    obtain ⟨width, x, rfl⟩ := shape
    rcases width with rfl | rfl | rfl
    all_goals simp [rvDecoderFields] at fields
    all_goals subst fields
    · exact ⟨⟨true, true, false, z, z, z, z, z, rs1, rs2, 0, x, s⟩, rfl, rfl, rfl, fun h => by cases h⟩
    · exact ⟨⟨true, false, false, z, z, z, z, z, rs1, rs2, 0, x, s⟩, rfl, rfl, rfl, fun h => by cases h⟩
  all_goals simp [rvDecoderFields] at fields

/-- `rv_query_facts` for the family's own entry (no pooled registry), for any field with `33554432 < p`. -/
theorem rv_entry_query_facts {p : Nat} [Fact p.Prime] (hp : 33554432 < p) {w : Nat → ZMod p}
    {setup : Table (ZMod p) (fields 9)}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    {input : RVInput} {entry : RVProgramEntry} (data : entry.data = rvData input)
    (query : decoderQuery w = entry.query) :
    w 10 = (if input.store then 1 else 0) ∧ w 11 = (if input.byte then 1 else 0) ∧
    (input.store = false → w 12 = if input.signed then 1 else 0) ∧
    (⟨(w 0).val, (w 1).val⟩ : Word) = Word.ofBitVec entry.pc ∧
    (⟨(w 8).val, (w 9).val⟩ : Word) = Word.ofBitVec (input.encodedImmediate.signExtend 32) ∧
    w 5 = (input.rs1.toNat : ZMod p) ∧
    (input.store = true → w 6 = (input.rs2.toNat : ZMod p)) ∧
    (input.store = false → w 7 = (input.rd.toNat : ZMod p)) := by
  have limbSize : limbBase < p := by dsimp [limbBase]; omega
  have q (k : Fin 9) := congrArg (fun v : Vector (ZMod p) 9 => v[k]) query
  have q0 := q 0
  have q1 := q 1
  have q2 := q 2
  have q3 := q 3
  have q4 := q 4
  have q5 := q 5
  have q6 := q 6
  have q8 := q 8
  change w 0 = ((Word.ofBitVec entry.pc).lo : ZMod p) at q0
  change w 1 = ((Word.ofBitVec entry.pc).hi : ZMod p) at q1
  change w 5 = (entry.data.rs1.toNat : ZMod p) at q2
  change w 6 = (entry.data.rs2.toNat : ZMod p) at q3
  change w 7 = (entry.data.rd.toNat : ZMod p) at q4
  change w 8 = (entry.data.immediate.lo : ZMod p) at q5
  change w 9 = (entry.data.immediate.hi : ZMod p) at q6
  change (∑ i : Fin 3, (2 ^ i.val : Nat) * w #[10, 11, 12][i]) = (entry.data.mask : ZMod p) at q8
  rw [data] at q2 q3 q4 q5 q6 q8
  have boolean : ∀ i : Fin 3, w #[10, 11, 12][i] = 0 ∨ w #[10, 11, 12][i] = 1 := by
    intro i
    fin_cases i
    · exact local_flags h 1
    · exact local_flags h 2
    · exact local_flags h 3
  have small : (rvData input).mask < 512 := by
    cases hs : input.store <;> cases hb : input.byte <;> cases hg : input.signed <;>
      simp [rvData, hs, hb, hg]
  have bits := Trace.Proofs.unpack_decoder_bits_of_width (by omega) (by decide) small boolean q8
  have b0 := bits 0
  have b1 := bits 1
  have b2 := bits 2
  refine ⟨?_, ?_, ?_, ?_, ?_, q2, ?_, ?_⟩
  · cases hs : input.store <;> cases hb : input.byte <;> cases hg : input.signed <;>
      simpa [rvData, hs, hb, hg, Nat.testBit] using b0
  · cases hs : input.store <;> cases hb : input.byte <;> cases hg : input.signed <;>
      simpa [rvData, hs, hb, hg, Nat.testBit] using b1
  · intro hs
    cases hb : input.byte <;> cases hg : input.signed <;>
      simpa [rvData, hs, hb, hg, Nat.testBit] using b2
  · have bound := Word.ofBitVec_bound entry.pc
    rw [q0, q1, ZMod.val_natCast_of_lt (lt_trans bound.1 limbSize),
      ZMod.val_natCast_of_lt (lt_trans bound.2 limbSize)]
  · have bound := Word.ofBitVec_bound (input.encodedImmediate.signExtend 32)
    change w 8 = ((Word.ofBitVec (input.encodedImmediate.signExtend 32)).lo : ZMod p) at q5
    change w 9 = ((Word.ofBitVec (input.encodedImmediate.signExtend 32)).hi : ZMod p) at q6
    rw [q5, q6, ZMod.val_natCast_of_lt (lt_trans bound.1 limbSize),
      ZMod.val_natCast_of_lt (lt_trans bound.2 limbSize)]
  · intro hs
    simpa [rvData, hs] using q3
  · intro hs
    simpa [rvData, hs] using q4

/-- One RAM subword row is one `RV.exec` of its entry's instruction, agreeing with the row's RV history and final PC.
    -/
theorem rv_row_step {p : Nat} [Fact p.Prime] (hp : 33554432 < p) (inverse : (-3840 : ZMod p) * 524288 = 1)
    {values : Nat → BitVec 32} {w : Nat → ZMod p}
    (core : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints (Verification.subwordTable values)))
    (active : w 4 = 1)
    {entry : RVProgramEntry} (query : decoderQuery w = entry.query)
    {i : RV.Instr} (decodes : RV.decode entry.bits = some i) (fields : rvDecoderFields i = some entry.data)
    (sourceBound : (Word.mk (w 19).val (w 20).val).Bounded) (readBound : (Word.mk (w 25).val (w 26).val).Bounded)
    (oldBound : (Word.mk (w 31).val (w 32).val).Bounded)
    {cells : List Cell} (aligned : ∀ cell ∈ cells, cell.Aligned)
    (ramDomain : ∀ address, Cell.ram address ∈ cells → RV.ROM_END ≤ address.toNat)
    (epoch : Nat) {before after : RV.State} (pc : before.pc = entry.pc)
    (history : RVHistory cells (rowEvents epoch (⟨.subwordMemory, w⟩ : Row p TraceKind)).reverse before after) :
    ∃ next, RV.exec before i = some next ∧
      RV.Same next { after with pc := (⟨.subwordMemory, w⟩ : Row p TraceKind).finish.word.toBitVec } := by
  have limbSize : limbBase < p := by dsimp [limbBase]; omega
  have arithmeticInverse : (-30720 : ZMod p) * 65536 = 1 := by
    calc
      (-30720 : ZMod p) * 65536 = (-3840 : ZMod p) * 524288 := by ring
      _ = 1 := inverse
  have oneValue : (1 : ZMod p).val = 1 := by
    simpa only [Nat.cast_one] using ZMod.val_natCast_of_lt (by omega : 1 < p)
  obtain ⟨input, rfl, rfl, data, loadNonzero⟩ := rv_fields_input decodes fields before
  obtain ⟨selected, byteSelected, signSelected, pcWord, immediateWord, rs1Query, rs2Query, rdQuery⟩ :=
    rv_entry_query_facts hp core data query
  -- PC successor.
  have pcBound : (Word.mk (w 0).val (w 1).val).Bounded := by
    rw [pcWord]; exact Word.ofBitVec_bound entry.pc
  have pcNext := pc_successor (by omega) arithmeticInverse core (initial := Word.mk (w 0).val (w 1).val)
    (final := Word.mk (w 13).val (w 14).val)
    ⟨(ZMod.natCast_zmod_val _).symm, (ZMod.natCast_zmod_val _).symm, rfl, rfl⟩ pcBound
  have finalPC : (⟨.subwordMemory, w⟩ : Row p TraceKind).finish.word.toBitVec = input.before.pc + 4 := by
    change (Word.mk (w 13).val (w 14).val).toBitVec = _
    rw [pcNext.2.2, pcWord, Word.ofBitVec_roundtrip, pc]
  -- Operand words.
  have offsetImmediate : input.encodedImmediate.signExtend 32 = (Word.mk (w 8).val (w 9).val).toBitVec := by
    rw [immediateWord, Word.ofBitVec_roundtrip]
  have immediateBound : (Word.mk (w 8).val (w 9).val).Bounded := by
    rw [immediateWord]
    exact Word.ofBitVec_bound _
  -- The row's ports in the pre-state, and the destination update.
  have shaped : RVHistory cells (nativeRowEvents epoch importedConstraintsTraceColumns
      #[importedConstraintsMemoryPorts[0], importedConstraintsMemoryPorts[1], importedConstraintsMemoryPorts[2]]
      w).reverse input.before after := history
  obtain ⟨firstCell, _, secondCell, secondMember, thirdCell, thirdMember, firstAddress, firstRead,
      secondAddress, secondRead, thirdAddress, thirdRead, thirdWrite⟩ :=
    rv_three_ports epoch (by simp [importedConstraintsMemoryPorts]) (by simp [importedConstraintsMemoryPorts]) shaped
  have valueRs1 : (w 5).val = input.rs1.toNat := by
    rw [rs1Query, ZMod.val_natCast, Nat.mod_eq_of_lt (by have := input.rs1.isLt; omega)]
  have firstIs : firstCell = .register input.rs1 := cell_address_injective (by
    rw [firstAddress]
    simp [importedConstraintsMemoryPorts, MemoryAddress.code, Cell.addressCode, valueRs1])
  subst firstIs
  have sourceRead : input.before.getReg input.rs1 = (Word.mk (w 19).val (w 20).val).toBitVec := by
    rw [readRV_register] at firstRead
    rw [Option.some.inj firstRead]
    simp [importedConstraintsMemoryPorts, MemoryPort.readCode, pairCode, memoryWord]
  have secondWord : memoryWord ((importedConstraintsMemoryPorts[1]).readCode w) =
      (Word.mk (w 25).val (w 26).val).toBitVec := by
    simp [importedConstraintsMemoryPorts, MemoryPort.readCode, pairCode, memoryWord]
  have thirdWord : memoryWord ((importedConstraintsMemoryPorts[2]).readCode w) =
      (Word.mk (w 31).val (w 32).val).toBitVec := by
    simp [importedConstraintsMemoryPorts, MemoryPort.readCode, pairCode, memoryWord]
  have writtenWord : memoryWord ((importedConstraintsMemoryPorts[2]).writeCode w) =
      (Word.mk (w 33).val (w 34).val).toBitVec := by
    simp [importedConstraintsMemoryPorts, MemoryPort.writeCode, pairCode, memoryWord]
  rw [secondWord] at secondRead
  rw [thirdWord] at thirdRead
  rw [writtenWord] at thirdWrite
  -- The byte offset inside the aligned cell.
  obtain ⟨highByte, bit0⟩ : ∃ b : Bool, w 35 = if b then 1 else 0 := by
    have flag : w 35 = 0 ∨ w 35 = 1 := local_flags core 4
    rcases flag with zero | one
    · exact ⟨false, by simp [zero]⟩
    · exact ⟨true, by simp [one]⟩
  obtain ⟨highHalf, bit1⟩ : ∃ b : Bool, w 36 = if b then 1 else 0 := by
    have flag : w 36 = 0 ∨ w 36 = 1 := local_flags core 5
    rcases flag with zero | one
    · exact ⟨false, by simp [zero]⟩
    · exact ⟨true, by simp [one]⟩
  have lowVal : (w 35).val = (if highByte then 1 else 0) := by
    rw [bit0]; cases highByte <;> simp [oneValue]
  have highVal : (w 36).val = (if highHalf then 1 else 0) := by
    rw [bit1]; cases highHalf <;> simp [oneValue]
  have halfAligned : input.byte = false → highByte = false := by
    intro half
    have zero := halfword_aligned core (by simpa [half] using byteSelected)
    have natural : (w 35).val = 0 := by rw [zero]; simp
    rw [lowVal] at natural
    cases eq : highByte <;> simp [eq] at natural ⊢
  let offset := (if highByte then 1 else 0) + 2 * (if highHalf then 1 else 0)
  have width : (if input.byte then 1 else 2) = 1 ∨ (if input.byte then 1 else 2) = 2 := by
    cases input.byte <;> simp
  have offsetWidth : offset + (if input.byte then 1 else 2) ≤ 4 := by
    cases hb : input.byte
    · have low := halfAligned hb
      cases highHalf <;> simp [offset, low]
    · cases highByte <;> cases highHalf <;> simp [offset]
  have offsetAligned : offset % (if input.byte then 1 else 2) = 0 := by
    cases hb : input.byte
    · have low := halfAligned hb
      cases highHalf <;> simp [offset, low]
    · simp [Nat.mod_one]
  -- The aligned cell `a` of the row's memory port; the access is at `a + offset`.
  have cellFacts : ∀ (a : BitVec 32), Word.mk (if input.store then w 27 else w 21).val
      (if input.store then w 28 else w 22).val = Word.ofBitVec a →
      input.before.getReg input.rs1 + input.encodedImmediate.signExtend 32 = a + BitVec.ofNat 32 offset := by
    intro a cellIs
    have address := effective_address (by omega) arithmeticInverse input.store core selected
      (source := Word.mk (w 19).val (w 20).val) (immediate := Word.mk (w 8).val (w 9).val)
      (cell := Word.mk (if input.store then w 27 else w 21).val (if input.store then w 28 else w 22).val)
      ⟨(ZMod.natCast_zmod_val _).symm, (ZMod.natCast_zmod_val _).symm,
        (ZMod.natCast_zmod_val _).symm, (ZMod.natCast_zmod_val _).symm,
        rfl, (ZMod.natCast_zmod_val _).symm⟩ sourceBound immediateBound
      (by rw [cellIs]; exact (Word.ofBitVec_bound a).2)
    simp only [lowVal, highVal] at address
    rw [cellIs, Word.ofBitVec_roundtrip] at address
    rw [sourceRead, offsetImmediate]
    exact address.2.2.2.1.symm
  cases hs : input.store
  · -- Loads: the second port reads the aligned RAM cell, the third writes rd.
    simp only [hs, Bool.false_eq_true, ite_false] at selected cellFacts
    have load : w 10 = 0 := selected
    have rd0 := loadNonzero hs
    have signs := signSelected hs
    cases secondCell with
    | register j =>
      simp [importedConstraintsMemoryPorts, MemoryAddress.code, Cell.addressCode, load, pairCode,
        oneValue] at secondAddress
    | ram a =>
    have tagged : Nat.pair 1 (Nat.pair (w 21).val (w 22).val) = (Cell.ram a).addressCode := by
      rw [secondAddress]
      simp [importedConstraintsMemoryPorts, MemoryAddress.code, load, pairCode, oneValue]
    obtain ⟨_, loEq, hiEq⟩ := RVWritable.ram_code_limbs a 1 (w 21) (w 22) tagged
    have cellIs : Word.mk (w 21).val (w 22).val = Word.ofBitVec a := by rw [loEq, hiEq]
    have cellBound : (Word.mk (w 21).val (w 22).val).Bounded := cellIs ▸ Word.ofBitVec_bound a
    have cellAligned : a.toNat % 4 = 0 := aligned _ secondMember
    have target := cellFacts a cellIs
    have readable := readable_of_readRV secondRead
    rw [readRV_ram _ readable] at secondRead
    have ramRead := Option.some.inj secondRead
    have classified := rom_selection (by omega) false core (by simpa using load)
      (address := Word.mk (w 21).val (w 22).val) (ZMod.natCast_zmod_val _).symm cellBound
    -- The cell is tracked RAM, so it lies above the ROM region: the row reads RAM.
    have high : RV.ROM_END ≤ a.toNat := by
      have outside := ramDomain a secondMember
      unfold RV.ROM_END
      unfold RV.ROM_END at outside
      omega
    have inRAM : ¬ (w 22).val < 64 := by
      intro low
      have hiA : (Word.ofBitVec a).hi = (w 22).val := by rw [← cellIs]
      dsimp [Word.ofBitVec, limbBase] at hiA
      unfold RV.ROM_END at high
      omega
    have ram : w 41 = 0 := by simpa [inRAM] using classified.1
    have loaded := rv_ram_load_data (by omega) input.byte input.signed highByte highHalf core active load ram
      byteSelected signs bit0 bit1 ⟨(ZMod.natCast_zmod_val _).symm, (ZMod.natCast_zmod_val _).symm⟩
      readBound halfAligned
    have value : (Word.mk (w 33).val (w 34).val).toBitVec = RV.extendLoad input.signed
        ((RV.read input.before.loadView a 4 >>> (8 * offset)).setWidth (8 * (if input.byte then 1 else 2))) := by
      rw [loaded.2, RV.read_loadView_ram _ _ _ high (by have := a.isLt; omega), ramRead]
    -- The third port writes rd.
    have registers := register_address false core (by simpa using load)
    simp only [Bool.false_eq_true, ite_false] at registers
    have valueRd : (w 7).val = input.rd.toNat := by
      rw [rdQuery hs, ZMod.val_natCast, Nat.mod_eq_of_lt (by have := input.rd.isLt; omega)]
    have thirdIs : thirdCell = .register input.rd := cell_address_injective (by
      rw [thirdAddress]
      simp [importedConstraintsMemoryPorts, MemoryAddress.code, Cell.addressCode, load, pairCode,
        registers.1, registers.2, valueRd])
    subst thirdIs
    have written := rv_register_update thirdWrite
    have exec := RV.exec_load_subword input.before _ width input.signed input.rd input.rs1 _ a offset rd0 target
      cellAligned offsetWidth offsetAligned
    simp only [rvInstruction, hs, Bool.false_eq_true, ite_false]
    rw [exec]
    refine ⟨_, rfl, rv_same_next ?_ finalPC⟩
    rw [← value]
    exact written
  · -- Stores: the second port reads rs2, the third reads and writes the aligned RAM cell.
    simp only [hs, ite_true] at selected cellFacts
    have store : w 10 = 1 := selected
    have registers := register_address true core (by simpa using store)
    simp only [ite_true] at registers
    have valueRs2 : (w 6).val = input.rs2.toNat := by
      rw [rs2Query hs, ZMod.val_natCast, Nat.mod_eq_of_lt (by have := input.rs2.isLt; omega)]
    have secondIs : secondCell = .register input.rs2 := cell_address_injective (by
      rw [secondAddress]
      simp [importedConstraintsMemoryPorts, MemoryAddress.code, Cell.addressCode, store, pairCode,
        registers.1, registers.2, valueRs2])
    subst secondIs
    rw [readRV_register] at secondRead
    have storedRead := Option.some.inj secondRead
    cases thirdCell with
    | register j =>
      simp [importedConstraintsMemoryPorts, MemoryAddress.code, Cell.addressCode, store, pairCode,
        oneValue] at thirdAddress
    | ram a =>
    have tagged : Nat.pair 1 (Nat.pair (w 27).val (w 28).val) = (Cell.ram a).addressCode := by
      rw [thirdAddress]
      simp [importedConstraintsMemoryPorts, MemoryAddress.code, store, pairCode, oneValue]
    obtain ⟨_, loEq, hiEq⟩ := RVWritable.ram_code_limbs a 1 (w 27) (w 28) tagged
    have cellIs : Word.mk (w 27).val (w 28).val = Word.ofBitVec a := by rw [loEq, hiEq]
    have cellBound : (Word.mk (w 27).val (w 28).val).Bounded := cellIs ▸ Word.ofBitVec_bound a
    have cellAligned : a.toNat % 4 = 0 := aligned _ thirdMember
    have target := cellFacts a cellIs
    have rom := RVWritable.subword_store_ram_writable (by omega) _ w core a thirdAddress.symm
    have readable := readable_of_readRV thirdRead
    rw [readRV_ram _ readable] at thirdRead
    have oldRead := Option.some.inj thirdRead
    have classified := rom_selection (by omega) true core (by simpa using store)
      (address := Word.mk (w 27).val (w 28).val) (ZMod.natCast_zmod_val _).symm cellBound
    have ram : w 41 = 0 := by
      have high : 64 ≤ (w 28).val := classified.2 rfl
      simpa [show ¬ (w 28).val < 64 by omega] using classified.1
    -- The merged word: rs2's low bytes at `offset`, the old cell bytes elsewhere.
    have encoded := store_byte_encoding (by omega) input.byte highByte highHalf core active store ram
      byteSelected bit0 bit1
      ⟨(ZMod.natCast_zmod_val _).symm, (ZMod.natCast_zmod_val _).symm, (ZMod.natCast_zmod_val _).symm⟩
      readBound oldBound halfAligned
    rw [← storedRead, ← oldRead] at encoded
    have exec := RV.exec_store_subword input.before _ width input.rs2 input.rs1 _ a _ offset target cellAligned
      rom offsetWidth offsetAligned encoded
    have written := rv_ram_update thirdWrite
    simp only [rvInstruction, hs, ite_true]
    rw [exec]
    exact ⟨_, rfl, rv_same_next written finalPC⟩

/-- Every row of an accepted RV-decoded trace preserves x0. -/
theorem rv_zero_preserving {p : Nat} [Fact p.Prime] (hp : limbBase < p)
    {trace : NativeTrace p} (accepted : Accepted trace) {initial : RV.State} {addresses : List (BitVec 32)}
    {program : List RVProgramEntry}
    (image : rvProgramImageWith rvDecoderFields initial addresses = some program)
    (decoded : RVDecoded trace program) : ZeroPreserving trace := by
  intro row member
  obtain ⟨entry, present, _, query⟩ := rv_decoder_member (decoded row member)
  obtain ⟨_, _, i, _, fields⟩ := rvProgram_entry_fetch image entry present
  have core := Verification.holds_of_sublist (accepted.constraints _ member)
    (List.sublist_append_left (importedConstraints trace.rom) importedConstraintsTimestampLookups)
  exact RVZero.subword_row_zero_preserving hp row trace.rom core entry fields query

/-- `SubwordMemory.RVRamTraceSoundnessClaim`, proved. -/
theorem rv_ram_trace_execution {p : Nat} [Fact p.Prime] (hp : 33554432 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1)
    {trace : NativeTrace p} {initial : RV.State} {cells : List Cell} {program : List RVProgramEntry}
    (inputs : RVRAMInputs trace initial cells program)
    (accepted : Accepted trace) (decoded : RVDecoded trace program) :
    RVRealizes trace initial cells := by
  have clockSize : 2 * timestampBase + 4 < p := by dsimp [timestampBase]; omega
  have limbSize : limbBase < p := by dsimp [limbBase]; omega
  obtain ⟨addresses, image⟩ := inputs.programImage
  obtain ⟨values, setup⟩ := inputs.setup
  have bounds := (native_value_bounds hp inverse accepted inputs.clocks
    (RVValues.rv_image_bounds inputs.image) setup).1
  refine rv_family_realizes clockSize inverse accepted inputs.toRVNativeInputs
    (rv_zero_preserving limbSize accepted image decoded)
    (rv_family_row_steps limbSize image (fun _ _ => True)
      (fun row member => by
        obtain ⟨entry, present, _, query⟩ := rv_decoder_member (decoded row member)
        exact ⟨entry, present, trivial, query⟩) ?_)
  intro row member entry _ _ query i decodes fields _ before after pc _ history
  obtain ⟨family, w⟩ := row
  cases family
  have core := Verification.holds_of_sublist (accepted.constraints _ member)
    (List.sublist_append_left (importedConstraints trace.rom) importedConstraintsTimestampLookups)
  change FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints trace.rom) at core
  rw [setup] at core
  have active : w 4 = 1 := accepted.active _ member
  have portBound (k : Fin 3) := bounds _ member importedConstraintsMemoryPorts[k]
    (by change importedConstraintsMemoryPorts[k] ∈ importedConstraintsMemoryPorts
        fin_cases k <;> simp [importedConstraintsMemoryPorts])
  have sourceBound : (Word.mk (w 19).val (w 20).val).Bounded := by
    simpa [read_word, importedConstraintsMemoryPorts] using portBound 0
  have readBound : (Word.mk (w 25).val (w 26).val).Bounded := by
    simpa [read_word, importedConstraintsMemoryPorts] using portBound 1
  have oldBound : (Word.mk (w 31).val (w 32).val).Bounded := by
    simpa [read_word, importedConstraintsMemoryPorts] using portBound 2
  exact rv_row_step hp inverse core active query decodes fields sourceBound readBound oldBound inputs.aligned
    inputs.ramDomain trace.memoryEpoch pc history

end Airbender.SubwordMemory.Proofs
