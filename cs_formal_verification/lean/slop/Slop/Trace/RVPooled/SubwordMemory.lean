module
public import Slop.Trace.RVPooledStep
public import Slop.Trace.RVPooledRow
public import Slop.SubwordMemory.RVTraceSoundness
public import Slop.ISA.RV.DecodeShape

@[expose] public section

/-! One LB/LBU/LH/LHU/SB/SH row of a pooled trace is one `RV.exec` of its instruction (`RVPooledRowStep`), from the
    row's own RV history: the row calculation of `SubwordMemory.Proofs.rv_trace_soundness` (`effective_address`,
    `rom_selection`, `rv_ram_load_data`/`rv_rom_load_data`, `store_byte_encoding`, `pc_successor`) with the three
    ports read off the history (`rv_three_ports`): rs1, then the aligned RAM cell (loads) or rs2 (stores), then rd
    (loads) or the cell's old word (stores), whose write is the row's result. -/

namespace Airbender.Trace.Proofs
open Arithmetic SubwordMemory SubwordMemory.Proofs

theorem rv_subword_shape {i : RV.Instr} {d : DecoderData Unit} (fields : SubwordMemory.rvDecoderFields i = some d)
    (shape : RV.Shape i) (s : RV.State) : ∃ input : RVInput, input.before = s ∧ i = rvInstruction input := by
  cases i with
  | load n sg rd rs1 off =>
    obtain ⟨size, x, rfl⟩ := shape
    rcases size with rfl | rfl | rfl <;> cases sg <;> simp [SubwordMemory.rvDecoderFields] at fields
    · exact ⟨⟨false, true, false, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, rs1, 0, rd, x, s⟩, rfl, rfl⟩
    · exact ⟨⟨false, true, true, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, rs1, 0, rd, x, s⟩, rfl, rfl⟩
    · exact ⟨⟨false, false, false, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, rs1, 0, rd, x, s⟩, rfl, rfl⟩
    · exact ⟨⟨false, false, true, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, rs1, 0, rd, x, s⟩, rfl, rfl⟩
  | store n rs2 rs1 off =>
    obtain ⟨size, x, rfl⟩ := shape
    rcases size with rfl | rfl | rfl <;> simp [SubwordMemory.rvDecoderFields] at fields
    · exact ⟨⟨true, true, false, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, rs1, rs2, 0, x, s⟩, rfl, rfl⟩
    · exact ⟨⟨true, false, false, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, rs1, rs2, 0, x, s⟩, rfl, rfl⟩
  | _ => simp [SubwordMemory.rvDecoderFields] at fields

theorem rv_subword_row_step {p : Nat} [Fact p.Prime] (hp : 536870912 ≤ p)
    (inverse : (-3840 : ZMod p) * 524288 = 1) {trace : PooledTrace p} {initial : RV.State} {cells : List Cell}
    {w : Nat → ZMod p} {before after : RV.State} {entry : RVPooledProgramEntry} {i : RV.Instr}
    (facts : RVPooledRowFacts trace initial cells ⟨.subwordMemory, w⟩ before after entry)
    (fields : rvPooledDecoderFields i = some entry.data) (decodes : RV.decode entry.bits = some i) :
    RVPooledRowStep ⟨.subwordMemory, w⟩ before after i := by
  have core := Verification.holds_of_sublist facts.constraints
    (List.sublist_append_left (importedConstraints trace.rom.subwordMemory) importedConstraintsTimestampLookups)
  change FlatOperation.ConstraintsHoldFlat (Verification.environment w)
    (importedConstraints trace.rom.subwordMemory) at core
  rw [facts.subwordTable] at core
  have active : w 4 = 1 := facts.active
  have arithmeticInverse : (-30720 : ZMod p) * 65536 = 1 := by
    calc
      (-30720 : ZMod p) * 65536 = (-3840 : ZMod p) * 524288 := by ring
      _ = 1 := inverse
  have oneValue : (1 : ZMod p).val = 1 := by
    simpa only [Nat.cast_one] using ZMod.val_natCast_of_lt (by omega : 1 < p)
  obtain ⟨d, fd, _⟩ := (rv_pooled_fields_family fields).2.2.2.2 facts.family
  obtain ⟨input, rfl, rfl⟩ := rv_subword_shape fd (RV.decode_shape decodes) before
  obtain ⟨loadNonzero, data⟩ := rv_pooled_fields fields facts.family
  obtain ⟨selected, byteSelected, signSelected, pcWord, immediateWord, rs1Query, rs2Query, rdQuery⟩ :=
    rv_query_facts hp core data facts.query
  -- PC successor.
  have pcNext := pc_successor (by omega) arithmeticInverse core
    (initial := Word.ofBitVec entry.pc) (final := Word.mk (w 13).val (w 14).val)
    ⟨by rw [← pcWord]; exact (ZMod.natCast_zmod_val _).symm,
     by rw [← pcWord]; exact (ZMod.natCast_zmod_val _).symm, rfl, rfl⟩ (Word.ofBitVec_bound entry.pc)
  have finish : (⟨.subwordMemory, w⟩ : Row p PooledFamily).finish.word.toBitVec = input.before.pc + 4 := by
    change (Word.mk (w 13).val (w 14).val).toBitVec = _
    rw [pcNext.2.2, Word.ofBitVec_roundtrip, facts.pc]
  -- Operand words.
  have offsetImmediate : input.encodedImmediate.signExtend 32 = (Word.mk (w 8).val (w 9).val).toBitVec := by
    rw [immediateWord, Word.ofBitVec_roundtrip]
  have immediateBound : (Word.mk (w 8).val (w 9).val).Bounded := by
    rw [immediateWord]
    exact Word.ofBitVec_bound _
  have portBound (k : Fin 3) := facts.readBounds importedConstraintsMemoryPorts[k]
    (by change importedConstraintsMemoryPorts[k] ∈ importedConstraintsMemoryPorts
        fin_cases k <;> simp [importedConstraintsMemoryPorts])
  have sourceBound : (Word.mk (w 19).val (w 20).val).Bounded := by
    simpa [read_word, importedConstraintsMemoryPorts] using portBound 0
  have readBound : (Word.mk (w 25).val (w 26).val).Bounded := by
    simpa [read_word, importedConstraintsMemoryPorts] using portBound 1
  have oldBound : (Word.mk (w 31).val (w 32).val).Bounded := by
    simpa [read_word, importedConstraintsMemoryPorts] using portBound 2
  -- The row's three ports, read off its history.
  have shape : (⟨.subwordMemory, w⟩ : Row p PooledFamily).ports =
      #[importedConstraintsMemoryPorts[0], importedConstraintsMemoryPorts[1],
        importedConstraintsMemoryPorts[2]] := by
    have portsEq : (⟨.subwordMemory, w⟩ : Row p PooledFamily).ports = importedConstraintsMemoryPorts := by rfl
    rw [portsEq]
    rfl
  have history := facts.history
  dsimp only [rowEvents] at history
  rw [shape] at history
  obtain ⟨firstCell, _, secondCell, secondMember, thirdCell, thirdMember, firstAddress, firstRead,
      secondAddress, secondRead, thirdAddress, thirdRead, thirdWrite⟩ :=
    rv_three_ports trace.memoryEpoch (by simp [importedConstraintsMemoryPorts])
      (by simp [importedConstraintsMemoryPorts]) history
  have boundP : 32 ≤ p := by omega
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
  have outputWord : memoryWord ((importedConstraintsMemoryPorts[2]).writeCode w) =
      (Word.mk (w 33).val (w 34).val).toBitVec := by
    simp [importedConstraintsMemoryPorts, MemoryPort.writeCode, pairCode, memoryWord]
  rw [secondWord] at secondRead
  rw [thirdWord] at thirdRead
  rw [outputWord] at thirdWrite
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
  -- The aligned cell is the RAM cell `a` of the row's memory port; the access is at `a + offset`.
  have cellFacts : ∀ (a : BitVec 32), Word.mk (if input.store then w 27 else w 21).val
      (if input.store then w 28 else w 22).val = Word.ofBitVec a →
      input.before.getReg input.rs1 + input.encodedImmediate.signExtend 32 = a + BitVec.ofNat 32 offset := by
    intro a cellIs
    have address := effective_address (by omega) arithmeticInverse input.store core selected
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
  · -- Loads: the second port reads the aligned RAM cell, ROM loads read the public subword ROM table.
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
    have aligned : a.toNat % 4 = 0 := facts.aligned _ secondMember
    have target := cellFacts a cellIs
    have readable := readable_of_readRV secondRead
    rw [readRV_ram _ readable] at secondRead
    have ramRead := Option.some.inj secondRead
    have classified := rom_selection (by omega) false core (by simpa using load)
      (address := Word.mk (w 21).val (w 22).val) (ZMod.natCast_zmod_val _).symm cellBound
    -- The loaded value: the extension of the cell word's slice at `offset`.
    have value : (Word.mk (w 33).val (w 34).val).toBitVec = RV.extendLoad input.signed
        ((RV.read input.before.loadView a 4 >>> (8 * offset)).setWidth (8 * (if input.byte then 1 else 2))) := by
      by_cases inROM : (w 22).val < 64
      · have rom : w 41 = 1 := by simpa [inROM] using classified.1
        have loaded := rv_rom_load_data (by omega) input.byte input.signed highByte highHalf core active load rom
          byteSelected signs bit0 bit1 ⟨rfl, (ZMod.natCast_zmod_val _).symm⟩ cellBound inROM halfAligned
        rw [loaded.2]
        congr 3
        -- The public ROM word of the cell is the ROM image's, which the row history never changes.
        have cellValue : (Word.mk (w 21).val (w 22).val).value = a.toNat := by
          rw [cellIs, ← Word.toBitVec_toNat (Word.ofBitVec_bound a), Word.ofBitVec_roundtrip]
        have below : a.toNat < RV.ROM_END := by
          rw [← cellValue]
          have low := cellBound.1
          unfold RV.ROM_END
          dsimp [Word.value, limbBase] at low ⊢
          omega
        rw [RV.read_loadView_rom _ _ _ (by unfold RV.ROM_END at below ⊢; omega), facts.rom, cellValue]
        have quarter : 4 * (a.toNat / 4) = a.toNat := by omega
        have inRAM : a.toNat + 4 ≤ RV.RAM_END := by
          unfold RV.ROM_END at below
          unfold RV.RAM_END
          omega
        simp only [ROM.wordsRV, inRAM, ite_true, quarter, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      · have ram : w 41 = 0 := by simpa [inROM] using classified.1
        have loaded := rv_ram_load_data (by omega) input.byte input.signed highByte highHalf core active load ram
          byteSelected signs bit0 bit1 ⟨(ZMod.natCast_zmod_val _).symm, (ZMod.natCast_zmod_val _).symm⟩
          readBound halfAligned
        have high : RV.ROM_END ≤ a.toNat := RVWritable.ram_index_rom_bound a (by rw [← hiEq]; omega)
        rw [loaded.2, RV.read_loadView_ram _ _ _ high (by have := a.isLt; omega), ramRead]
    have exec := RV.exec_load_subword input.before _ width input.signed input.rd input.rs1 _ a offset rd0 target
      aligned offsetWidth offsetAligned
    -- The third port writes rd.
    have rdIs : thirdCell.addressCode = (Cell.register input.rd).addressCode := by
      rw [thirdAddress]
      have registers := register_address false core (by simpa using load)
      simp only [Bool.false_eq_true, ite_false] at registers
      have valueRd : (w 27).val = input.rd.toNat := by
        rw [registers.1, rdQuery hs, ZMod.val_natCast, Nat.mod_eq_of_lt (by have := input.rd.isLt; omega)]
      simp [importedConstraintsMemoryPorts, MemoryAddress.code, Cell.addressCode, load, pairCode,
        registers.2, valueRd]
    have written := rv_apply_register rdIs thirdWrite
    simp only [rvInstruction, hs, Bool.false_eq_true, ite_false]
    refine ⟨_, exec, ?_⟩
    rw [← value]
    exact rv_register_next written finish
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
    have aligned : a.toNat % 4 = 0 := facts.aligned _ thirdMember
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
    have exec := RV.exec_store_subword input.before _ width input.rs2 input.rs1 _ a _ offset target aligned rom
      offsetWidth offsetAligned encoded
    simp only [rvInstruction, hs, ite_true]
    exact ⟨_, exec, rv_state_next (rv_apply_ram thirdWrite) rfl finish⟩

end Airbender.Trace.Proofs
