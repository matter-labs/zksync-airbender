module
public import Slop.Trace.RVPooledStep
public import Slop.Trace.RVPooledRow
public import Slop.WordMemory.RVTraceSoundness
public import Slop.ISA.RV.DecodeShape
public import Slop.Trace.RVPooled.Arithmetic
public import Slop.Defs.Helpers.Memory.Ports
public import Slop.Defs.Helpers.Memory.RowEvents
public import Slop.Defs.Helpers.Memory.History
public import Slop.Defs.Helpers.Core.Word

@[expose] public section

/-! One LW/SW row of a pooled trace is one `RV.exec` of its instruction (`RVPooledRowStep`), from the row's own RV
    history: the row calculation of `WordMemory.Proofs.rv_trace_soundness` (`effective_address`, `rom_selection`,
    `rom_data`/`ram_data`, `pc_successor`) with the three ports read off the history (`rv_three_ports`): rs1, then
    the RAM word (LW) or rs2 (SW), then the destination register (LW) or RAM word (SW). Every port cell is a tracked
    cell, so a RAM address is aligned. -/

namespace Airbender.Trace.Proofs
open Arithmetic WordMemory WordMemory.Proofs

theorem rv_word_shape {i : RV.Instr} {d : DecoderData} (fields : Trace.rvDecoderFields i = some d)
    (family : d.family = .wordMemory) (shape : RV.Shape i) (s : RV.State) :
    ∃ input : RVInput, input.before = s ∧ i = rvInstruction input := by
  rcases rv_arithmetic_cases fields with rfl | ⟨tag, -⟩ | ⟨-, ⟨rd, rs1, imm, -, rfl⟩ | ⟨rs2, rs1, imm, rfl⟩⟩
  · cases family
  · rw [tag] at family
    cases family
  · obtain ⟨-, x, rfl⟩ := shape
    exact ⟨⟨false, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, rs1, 0, rd, x, s⟩, rfl, rfl⟩
  · obtain ⟨-, x, rfl⟩ := shape
    exact ⟨⟨true, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, rs1, rs2, 0, x, s⟩, rfl, rfl⟩

/-- A word below `ROM_END` at an aligned address: limb form. -/
private theorem rom_address (a : BitVec 32) (high : (Word.ofBitVec a).hi < 64) : a.toNat < RV.ROM_END := by
  unfold RV.ROM_END
  dsimp [Word.ofBitVec, limbBase] at high
  omega

theorem rv_word_row_step {p : Nat} [Fact p.Prime] (hp : 536870912 ≤ p)
    (inverse : (-3840 : ZMod p) * 524288 = 1) {trace : PooledTrace p} {initial : RV.State} {cells : List Cell}
    {w : Nat → ZMod p} {before after : RV.State} {entry : RVPooledProgramEntry} {i : RV.Instr}
    (facts : RVPooledRowFacts trace initial cells ⟨.wordMemory, w⟩ before after entry)
    (fields : rvPooledDecoderFields i = some entry.data) (decodes : RV.decode entry.bits = some i) :
    RVPooledRowStep ⟨.wordMemory, w⟩ before after i := by
  have core := Verification.holds_of_sublist facts.constraints
    (List.sublist_append_left (importedConstraints trace.rom.wordMemory) importedConstraintsTimestampLookups)
  have arithmeticInverse : (-30720 : ZMod p) * 65536 = 1 := by
    calc
      (-30720 : ZMod p) * 65536 = (-3840 : ZMod p) * 524288 := by ring
      _ = 1 := inverse
  obtain ⟨d, fd, dataEq⟩ := (rv_pooled_fields_family fields).1 (Or.inr facts.family)
  have dFamily : d.family = .wordMemory := by
    have tag := facts.family
    rw [dataEq] at tag
    cases hf : d.family <;> simp [DecoderData.mapFamily, pooledArithmeticFamily, hf] at tag ⊢
  obtain ⟨input, rfl, rfl⟩ := rv_word_shape fd dFamily (RV.decode_shape decodes) before
  obtain ⟨loadNonzero, data⟩ := rv_word_fields fields facts.family
  obtain ⟨selected, pcWord, immediateWord, rs1Query, rs2Query, rdQuery⟩ := rv_query_facts hp data facts.query
  -- PC successor.
  have pcNext := pc_successor (by omega) arithmeticInverse core
    (initial := Word.ofBitVec entry.pc) (final := Word.mk (w 11).val (w 12).val)
    ⟨by rw [← pcWord]; exact (ZMod.natCast_zmod_val _).symm,
     by rw [← pcWord]; exact (ZMod.natCast_zmod_val _).symm, rfl, rfl⟩ (Word.ofBitVec_bound entry.pc)
  have finish : (⟨.wordMemory, w⟩ : Row p PooledFamily).finish.word.toBitVec = input.before.pc + 4 := by
    change (Word.mk (w 11).val (w 12).val).toBitVec = _
    rw [pcNext.2.2, Word.ofBitVec_roundtrip, facts.pc]
  -- Operand words.
  have offset : input.encodedImmediate.signExtend 32 = (Word.mk (w 8).val (w 9).val).toBitVec := by
    rw [immediateWord, Word.ofBitVec_roundtrip]
  have immediateBound : (Word.mk (w 8).val (w 9).val).Bounded := by
    rw [immediateWord]
    exact Word.ofBitVec_bound _
  have sourceBound : (Word.mk (w 17).val (w 18).val).Bounded := by
    have source := facts.readBounds importedConstraintsMemoryPorts[0]
      (by change importedConstraintsMemoryPorts[0] ∈ importedConstraintsMemoryPorts
          simp [importedConstraintsMemoryPorts])
    simpa [read_word, importedConstraintsMemoryPorts] using source
  -- The row's three ports, read off its history.
  have shape : (⟨.wordMemory, w⟩ : Row p PooledFamily).ports =
      #[importedConstraintsMemoryPorts[0], importedConstraintsMemoryPorts[1],
        importedConstraintsMemoryPorts[2]] := by
    have portsEq : (⟨.wordMemory, w⟩ : Row p PooledFamily).ports = importedConstraintsMemoryPorts := by rfl
    rw [portsEq]
    rfl
  have history := facts.history
  dsimp only [rowEvents] at history
  rw [shape] at history
  obtain ⟨firstCell, _, secondCell, secondMember, thirdCell, thirdMember, firstAddress, firstRead,
      secondAddress, secondRead, thirdAddress, _, thirdWrite⟩ :=
    rv_three_ports trace.memoryEpoch (by simp [importedConstraintsMemoryPorts])
      (by simp [importedConstraintsMemoryPorts]) history
  have boundP : 32 ≤ p := by omega
  have valueRs1 : (w 5).val = input.rs1.toNat := by
    rw [rs1Query, ZMod.val_natCast, Nat.mod_eq_of_lt (by have := input.rs1.isLt; omega)]
  have firstIs : firstCell = .register input.rs1 := cell_address_injective (by
    rw [firstAddress]
    simp [importedConstraintsMemoryPorts, MemoryAddress.code, Cell.addressCode, valueRs1])
  subst firstIs
  have sourceRead : input.before.getReg input.rs1 = (Word.mk (w 17).val (w 18).val).toBitVec := by
    rw [readRV_register] at firstRead
    rw [Option.some.inj firstRead]
    simp [importedConstraintsMemoryPorts, MemoryPort.readCode, pairCode, memoryWord]
  have secondWord : memoryWord ((importedConstraintsMemoryPorts[1]).readCode w) =
      (Word.mk (w 23).val (w 24).val).toBitVec := by
    simp [importedConstraintsMemoryPorts, MemoryPort.readCode, pairCode, memoryWord]
  rw [secondWord] at secondRead
  have outputWord : memoryWord ((importedConstraintsMemoryPorts[2]).writeCode w) =
      (Word.mk (w 31).val (w 32).val).toBitVec := by
    simp [importedConstraintsMemoryPorts, MemoryPort.writeCode, pairCode, memoryWord]
  rw [outputWord] at thirdWrite
  have disabled : ∀ query, trace.rom.wordMemory.Contains #[] query → query[8] = 0 →
      query[1] = 0 ∧ query[2] = 0 := by
    intro query contains inactive
    exact Trace.RVValues.rv_rom_disabled (by omega) (by rwa [facts.wordTable] at contains) inactive
  have oneValue : (1 : ZMod p).val = 1 := by
    simpa only [Nat.cast_one] using ZMod.val_natCast_of_lt (by omega : 1 < p)
  cases hs : input.store
  · -- LW: the second port reads the RAM cell at the effective address; the third writes rd.
    simp only [hs, Bool.false_eq_true, ite_false] at selected
    have rd0 := loadNonzero hs
    cases secondCell with
    | register j =>
      simp [importedConstraintsMemoryPorts, MemoryAddress.code, Cell.addressCode, selected, pairCode,
        oneValue] at secondAddress
    | ram a =>
    have tagged : Nat.pair 1 (Nat.pair (w 19).val (w 20).val) = (Cell.ram a).addressCode := by
      rw [secondAddress]
      simp [importedConstraintsMemoryPorts, MemoryAddress.code, selected, pairCode, oneValue]
    obtain ⟨_, loEq, hiEq⟩ := RVWritable.ram_code_limbs a 1 (w 19) (w 20) tagged
    have cellWord : Word.mk (w 19).val (w 20).val = Word.ofBitVec a := by rw [loEq, hiEq]
    have addressBound : (Word.mk (w 19).val (w 20).val).Bounded := cellWord ▸ Word.ofBitVec_bound a
    have aligned : a.toNat % 4 = 0 := facts.aligned _ secondMember
    have readable := readable_of_readRV secondRead
    rw [readRV_ram _ readable] at secondRead
    have ramRead := Option.some.inj secondRead
    have address := effective_address (by omega) arithmeticInverse false core
      (by simpa using selected)
      ⟨(ZMod.natCast_zmod_val _).symm, (ZMod.natCast_zmod_val _).symm,
        (ZMod.natCast_zmod_val _).symm, (ZMod.natCast_zmod_val _).symm,
        (ZMod.natCast_zmod_val _).symm, (ZMod.natCast_zmod_val _).symm⟩ sourceBound immediateBound addressBound
    rw [cellWord, Word.ofBitVec_roundtrip] at address
    have classified := rom_selection (by omega) false core (by simpa using selected)
      (address := Word.mk (w 19).val (w 20).val) (ZMod.natCast_zmod_val _).symm addressBound
    -- The loaded word: RAM copies the read word; ROM reads the public ROM image.
    have value : RV.read input.before.loadView a 4 = (Word.mk (w 31).val (w 32).val).toBitVec := by
      by_cases inROM : (w 20).val < 64
      · have flag : w 35 = 1 := by simpa [inROM] using classified.1
        have lookup := rom_data core selected facts.active flag
        rw [facts.wordTable] at lookup
        have rom := Trace.RVValues.rv_rom_read (by dsimp [RV.ROM_END]; omega)
          ⟨(w 19).val, (w 20).val⟩ (w 31) (w 32) addressBound inROM
          (by simpa only [ZMod.natCast_zmod_val] using lookup)
        rw [cellWord, Word.ofBitVec_roundtrip] at rom
        have below : a.toNat < RV.ROM_END := rom_address a (by rw [← hiEq]; exact inROM)
        rw [RV.read_loadView_rom _ _ _ (by unfold RV.ROM_END at below ⊢; omega), facts.rom]
        exact rom.2
      · have flag : w 35 = 0 := by simpa [inROM] using classified.1
        have copied := ram_data disabled false core (by simpa using selected) flag
        change w 31 = w 23 ∧ w 32 = w 24 at copied
        have high : RV.ROM_END ≤ a.toNat := RVWritable.ram_index_rom_bound a (by rw [← hiEq]; omega)
        rw [RV.read_loadView_ram _ _ _ high (by have := a.isLt; omega), ramRead, copied.1, copied.2]
    have target : input.before.getReg input.rs1 + input.encodedImmediate.signExtend 32 = a := by
      rw [sourceRead, offset, address]
    -- The third port writes rd.
    have rdIs : thirdCell.addressCode = (Cell.register input.rd).addressCode := by
      rw [thirdAddress]
      have registers := register_address false core (by simpa using selected)
      simp only [Bool.false_eq_true, ite_false] at registers
      have valueRd : (w 25).val = input.rd.toNat := by
        rw [registers.1, rdQuery hs, ZMod.val_natCast, Nat.mod_eq_of_lt (by have := input.rd.isLt; omega)]
      simp [importedConstraintsMemoryPorts, MemoryAddress.code, Cell.addressCode, selected, pairCode,
        registers.2, valueRd]
    have written := rv_apply_register rdIs thirdWrite
    refine ⟨(input.before.setReg input.rd (RV.read input.before.loadView a 4)).nextInstr, ?_, ?_⟩
    · simp only [rvInstruction, hs, Bool.false_eq_true, ite_false, RV.exec, target, rd0]
      rw [ite_eq_left ⟨aligned, readable⟩]
      simp
    · rw [value]
      exact rv_register_next written finish
  · -- SW: the second port reads rs2; the third writes the RAM cell at the effective address.
    simp only [hs, ite_true] at selected
    have registers := register_address true core (by simpa using selected)
    simp only [ite_true] at registers
    have valueRs2 : (w 6).val = input.rs2.toNat := by
      rw [rs2Query hs, ZMod.val_natCast, Nat.mod_eq_of_lt (by have := input.rs2.isLt; omega)]
    have secondIs : secondCell = .register input.rs2 := cell_address_injective (by
      rw [secondAddress]
      simp [importedConstraintsMemoryPorts, MemoryAddress.code, Cell.addressCode, selected, pairCode,
        registers.1, registers.2, valueRs2])
    subst secondIs
    rw [readRV_register] at secondRead
    have storedRead := Option.some.inj secondRead
    cases thirdCell with
    | register j =>
      simp [importedConstraintsMemoryPorts, MemoryAddress.code, Cell.addressCode, selected, pairCode,
        oneValue] at thirdAddress
    | ram a =>
    have tagged : Nat.pair 1 (Nat.pair (w 25).val (w 26).val) = (Cell.ram a).addressCode := by
      rw [thirdAddress]
      simp [importedConstraintsMemoryPorts, MemoryAddress.code, selected, pairCode, oneValue]
    obtain ⟨_, loEq, hiEq⟩ := RVWritable.ram_code_limbs a 1 (w 25) (w 26) tagged
    have cellWord : Word.mk (w 25).val (w 26).val = Word.ofBitVec a := by rw [loEq, hiEq]
    have addressBound : (Word.mk (w 25).val (w 26).val).Bounded := cellWord ▸ Word.ofBitVec_bound a
    have aligned : a.toNat % 4 = 0 := facts.aligned _ thirdMember
    have ram := RVWritable.word_store_ram_writable (by omega) trace.rom.wordMemory w core a thirdAddress.symm
    have writable : RV.writable a 4 := by
      have small := a.isLt
      refine ⟨ram, ?_⟩
      unfold RV.RAM_END
      omega
    have address := effective_address (by omega) arithmeticInverse true core
      (by simpa using selected)
      ⟨(ZMod.natCast_zmod_val _).symm, (ZMod.natCast_zmod_val _).symm,
        (ZMod.natCast_zmod_val _).symm, (ZMod.natCast_zmod_val _).symm,
        (ZMod.natCast_zmod_val _).symm, (ZMod.natCast_zmod_val _).symm⟩ sourceBound immediateBound addressBound
    rw [cellWord, Word.ofBitVec_roundtrip] at address
    have classified := rom_selection (by omega) true core (by simpa using selected)
      (address := Word.mk (w 25).val (w 26).val) (ZMod.natCast_zmod_val _).symm addressBound
    have flag : w 35 = 0 := by
      have high : 64 ≤ (w 26).val := classified.2 rfl
      simpa [show ¬ (w 26).val < 64 by omega] using classified.1
    have copied := ram_data disabled true core (by simpa using selected) flag
    change w 31 = w 23 ∧ w 32 = w 24 at copied
    have value : input.before.getReg input.rs2 = (Word.mk (w 31).val (w 32).val).toBitVec := by
      rw [storedRead, copied.1, copied.2]
    have target : input.before.getReg input.rs1 + input.encodedImmediate.signExtend 32 = a := by
      rw [sourceRead, offset, address]
    refine ⟨(input.before.store a (input.before.getReg input.rs2) 4).nextInstr, ?_, ?_⟩
    · simp only [rvInstruction, hs, ite_true, RV.exec, target]
      rw [ite_eq_left ⟨aligned, writable⟩]
    · rw [value]
      exact rv_state_next (rv_apply_ram thirdWrite) rfl finish

end Airbender.Trace.Proofs
