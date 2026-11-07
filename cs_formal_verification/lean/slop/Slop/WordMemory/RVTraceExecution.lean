import Slop.WordMemory
import Human.Helpers.Context.FamilyLayout
import Slop.WordMemory.RVQuery
import Slop.WordMemory.RVWritable
import Slop.Trace.RVValues
import Slop.Trace.RVRomRead
import Slop.Trace.RVFamilyTrace
import Slop.Trace.RVWritable
import Slop.ISA.RV.DecodeShape

/-! One word-memory row of the two-family (ADD/SUB + word memory) trace on the RV route: one `RV.exec` of its entry's
    instruction (LW to a register other than x0, or SW), agreeing with the row's RV history and final PC
    (`rv_row_step`). The per-row proof of `RVTraceSoundness.lean`, with the row's ports read from its RV history: LW
    reads RAM (the read word) or, below `ROM.limit`, the word-ROM table, which holds the ROM image (`rv_rom_read`);
    SW stores rs2 in RAM (`word_store_ram_writable`). -/

namespace Airbender.WordMemory.Proofs
open Arithmetic Trace Trace.Proofs

/-- A word-memory entry of a decoded instruction is the data of an RV input of the LW/SW claim (LW: rd ≠ x0). -/
theorem rv_fields_input {bits : RV.Word} {i : RV.Instr} {d : DecoderData}
    (decodes : RV.decode bits = some i) (fields : rvDecoderFields i = some d) (family : d.family = .wordMemory)
    (s : RV.State) :
    ∃ input : RVInput, input.before = s ∧ i = rvInstruction input ∧ d = rvData input ∧
      (input.store = false → input.rd ≠ 0) := by
  have shape := RV.decode_shape decodes
  let z : Word := ⟨0, 0⟩
  cases i
  case load n sg rd rs1 off =>
    simp only [RV.Shape] at shape
    obtain ⟨width, x, rfl⟩ := shape
    by_cases hz : rd = 0#5
    all_goals rcases width with rfl | rfl | rfl
    all_goals cases sg
    all_goals simp [rvDecoderFields, arithmeticFields, hz] at fields
    all_goals subst fields
    all_goals first
      | (cases family; done)
      | exact ⟨⟨false, z, z, z, z, rs1, 0, rd, x, s⟩, rfl, rfl, rfl, fun _ => hz⟩
  case store n rs2 rs1 off =>
    simp only [RV.Shape] at shape
    obtain ⟨width, x, rfl⟩ := shape
    rcases width with rfl | rfl | rfl
    all_goals simp [rvDecoderFields] at fields
    subst fields
    exact ⟨⟨true, z, z, z, z, rs1, rs2, 0, x, s⟩, rfl, rfl, rfl, fun h => by cases h⟩
  case op o rd rs1 rs2 =>
    by_cases hz : rd = 0#5
    all_goals cases o
    all_goals simp [rvDecoderFields, arithmeticFields, hz] at fields
    all_goals (subst fields; cases family)
  case opImm o rd rs1 imm =>
    by_cases hz : rd = 0#5
    all_goals cases o
    all_goals simp [rvDecoderFields, arithmeticFields, hz] at fields
    all_goals (subst fields; cases family)
  case lui rd imm =>
    by_cases hz : rd = 0#5
    all_goals simp [rvDecoderFields, arithmeticFields, hz] at fields
    all_goals (subst fields; cases family)
  case auipc rd imm =>
    by_cases hz : rd = 0#5
    all_goals simp [rvDecoderFields, arithmeticFields, hz] at fields
    all_goals (subst fields; cases family)
  case rev8 rd rs1 =>
    by_cases hz : rd = 0#5
    all_goals simp [rvDecoderFields, arithmeticFields, hz] at fields
    all_goals (subst fields; cases family)
  all_goals simp [rvDecoderFields] at fields

/-- A word below `ROM_END` at an aligned address: limb form. -/
private theorem rom_address (a : BitVec 32) (high : (Word.ofBitVec a).hi < 64) : a.toNat < RV.ROM_END := by
  unfold RV.ROM_END
  dsimp [Word.ofBitVec, limbBase] at high
  omega

/-- One word-memory row is one `RV.exec` of its entry's instruction, agreeing with the row's RV history and final PC.
    The word-ROM table holds the ROM image of `initial`, which the row's pre-state still has. -/
theorem rv_row_step {p : Nat} [Fact p.Prime] (hp : 536870912 ≤ p) (inverse : (-3840 : ZMod p) * 524288 = 1)
    {initial : RV.State} {cells : List Cell} {w : Nat → ZMod p}
    (core : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints (ROM.table cells (romImageRV initial cells))))
    (active : w 4 = 1)
    {entry : RVProgramEntry} (family : entry.data.family = .wordMemory)
    (query : (⟨.wordMemory, w⟩ : Row p).decoderQuery = entry.query)
    {i : RV.Instr} (decodes : RV.decode entry.bits = some i) (fields : rvDecoderFields i = some entry.data)
    (sourceBound : (Word.mk (w 17).val (w 18).val).Bounded)
    (aligned : ∀ cell ∈ cells, cell.Aligned)
    (epoch : Nat) {before after : RV.State} (pc : before.pc = entry.pc) (romSame : before.rom = initial.rom)
    (history : RVHistory cells (rowEvents epoch (⟨.wordMemory, w⟩ : Row p)).reverse before after) :
    ∃ next, RV.exec before i = some next ∧
      RV.Same next { after with pc := (⟨.wordMemory, w⟩ : Row p).finish.word.toBitVec } := by
  have limbSize : limbBase < p := by dsimp [limbBase]; omega
  have arithmeticInverse : (-30720 : ZMod p) * 65536 = 1 := by
    calc
      (-30720 : ZMod p) * 65536 = (-3840 : ZMod p) * 524288 := by ring
      _ = 1 := inverse
  have oneValue : (1 : ZMod p).val = 1 := by
    simpa only [Nat.cast_one] using ZMod.val_natCast_of_lt (by omega : 1 < p)
  obtain ⟨input, rfl, rfl, data, loadNonzero⟩ := rv_fields_input decodes fields family before
  let pooled : RVPooledProgramEntry := entry.mapFamily pooledArithmeticFamily
  have pooledData : pooled.data = (rvData input).mapFamily pooledArithmeticFamily := by
    simp only [pooled, RVProgramEntry.mapFamily, data]
  obtain ⟨selected, pcWord, immediateWord, rs1Query, rs2Query, rdQuery⟩ :=
    rv_query_facts hp pooledData (p := p) (w := w) query
  change _ = Word.ofBitVec entry.pc at pcWord
  -- PC successor.
  have pcBound : (Word.mk (w 0).val (w 1).val).Bounded := by
    rw [pcWord]; exact Word.ofBitVec_bound entry.pc
  have pcNext := pc_successor (by omega) arithmeticInverse core (initial := Word.mk (w 0).val (w 1).val)
    (final := Word.mk (w 11).val (w 12).val)
    ⟨(ZMod.natCast_zmod_val _).symm, (ZMod.natCast_zmod_val _).symm, rfl, rfl⟩ pcBound
  have finalPC : (⟨.wordMemory, w⟩ : Row p).finish.word.toBitVec = input.before.pc + 4 := by
    change (Word.mk (w 11).val (w 12).val).toBitVec = _
    rw [pcNext.2.2, pcWord, Word.ofBitVec_roundtrip, pc]
  -- Operand words.
  have offset : input.encodedImmediate.signExtend 32 = (Word.mk (w 8).val (w 9).val).toBitVec := by
    rw [immediateWord, Word.ofBitVec_roundtrip]
  have immediateBound : (Word.mk (w 8).val (w 9).val).Bounded := by
    rw [immediateWord]
    exact Word.ofBitVec_bound _
  -- The row's ports in the pre-state, and the destination update.
  have shaped : RVHistory cells (nativeRowEvents epoch importedConstraintsTraceColumns
      #[importedConstraintsMemoryPorts[0], importedConstraintsMemoryPorts[1], importedConstraintsMemoryPorts[2]]
      w).reverse input.before after := history
  obtain ⟨firstCell, _, secondCell, secondMember, thirdCell, thirdMember, firstAddress, firstRead,
      secondAddress, secondRead, thirdAddress, _, thirdWrite⟩ :=
    rv_three_ports epoch (by simp [importedConstraintsMemoryPorts]) (by simp [importedConstraintsMemoryPorts]) shaped
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
  have writtenWord : memoryWord ((importedConstraintsMemoryPorts[2]).writeCode w) =
      (Word.mk (w 31).val (w 32).val).toBitVec := by
    simp [importedConstraintsMemoryPorts, MemoryPort.writeCode, pairCode, memoryWord]
  rw [secondWord] at secondRead
  rw [writtenWord] at thirdWrite
  have disabled : ∀ query : Vector (ZMod p) 9, (ROM.table cells (romImageRV initial cells)).Contains #[] query →
      query[8] = 0 →
      query[1] = 0 ∧ query[2] = 0 := by
    intro query contains inactive
    exact Trace.RVValues.rv_rom_disabled (by omega) contains inactive
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
    have cellAligned : a.toNat % 4 = 0 := aligned _ secondMember
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
    -- The loaded word: RAM copies the read word; ROM reads the ROM image.
    have value : RV.read input.before.loadView a 4 = (Word.mk (w 31).val (w 32).val).toBitVec := by
      by_cases inROM : (w 20).val < 64
      · have flag : w 35 = 1 := by simpa [inROM] using classified.1
        have lookup := rom_data core selected active flag
        have rom := Trace.RVValues.rv_rom_read (by dsimp [ROM.limit]; omega)
          ⟨(w 19).val, (w 20).val⟩ (w 31) (w 32) addressBound inROM
          (by simpa only [ZMod.natCast_zmod_val] using lookup)
        rw [cellWord, Word.ofBitVec_roundtrip] at rom
        have below : a.toNat < RV.ROM_END := rom_address a (by rw [← hiEq]; exact inROM)
        rw [RV.read_loadView_rom _ _ _ (by unfold RV.ROM_END at below ⊢; omega), romSame]
        exact rom.2
      · have flag : w 35 = 0 := by simpa [inROM] using classified.1
        have copied := ram_data disabled false core (by simpa using selected) flag
        change w 31 = w 23 ∧ w 32 = w 24 at copied
        have high : RV.ROM_END ≤ a.toNat := RVWritable.ram_index_rom_bound a (by rw [← hiEq]; omega)
        rw [RV.read_loadView_ram _ _ _ high (by have := a.isLt; omega), ramRead, copied.1, copied.2]
    have target : input.before.getReg input.rs1 + input.encodedImmediate.signExtend 32 = a := by
      rw [sourceRead, offset, address]
    -- The third port writes rd.
    have registers := register_address false core (by simpa using selected)
    simp only [Bool.false_eq_true, ite_false] at registers
    have valueRd : (w 7).val = input.rd.toNat := by
      rw [rdQuery hs, ZMod.val_natCast, Nat.mod_eq_of_lt (by have := input.rd.isLt; omega)]
    have thirdIs : thirdCell = .register input.rd := cell_address_injective (by
      rw [thirdAddress]
      simp [importedConstraintsMemoryPorts, MemoryAddress.code, Cell.addressCode, selected, pairCode,
        registers.1, registers.2, valueRd])
    subst thirdIs
    have written := rv_register_update thirdWrite
    refine ⟨(input.before.setReg input.rd (RV.read input.before.loadView a 4)).nextInstr, ?_,
      rv_same_next (by rw [value]; exact written) finalPC⟩
    simp only [rvInstruction, hs, Bool.false_eq_true, ite_false, RV.exec, target, rd0]
    rw [if_pos ⟨cellAligned, readable⟩]
    simp
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
    have cellAligned : a.toNat % 4 = 0 := aligned _ thirdMember
    have ram := RVWritable.word_store_ram_writable (by omega) _ w core a thirdAddress.symm
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
    have written := rv_ram_update thirdWrite
    refine ⟨(input.before.store a (input.before.getReg input.rs2) 4).nextInstr, ?_,
      rv_same_next (by rw [value]; exact written) finalPC⟩
    simp only [rvInstruction, hs, ite_true, RV.exec, target]
    rw [if_pos ⟨cellAligned, writable⟩]

end Airbender.WordMemory.Proofs
