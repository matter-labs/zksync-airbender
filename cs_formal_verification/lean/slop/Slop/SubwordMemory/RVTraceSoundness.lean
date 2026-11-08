module
public import Human.Circuits.SubwordMemory.RVTheorems
public import Slop.SubwordMemory.RVQuery
public import Slop.SubwordMemory.RVData
public import Slop.SubwordMemory.RVWritable
public import Slop.SubwordMemory.Stores
public import Slop.Trace.RVPooledRow
public import Slop.Trace.RVRowGlue
public import Slop.Trace.RVRowReads

@[expose] public section

/-! RV32 LB/LBU/LH/LHU/SB/SH soundness (`RVSoundnessClaim`), on the RV route: no Sail state, interpreter,
    `Configured` or `OrdinaryWordAddress` fact.

    - Fetch/step: the row's program entry is an aligned word of the ROM image (`rvProgram_entry_fetch`);
      the row's pre-state has the entry's PC and the same ROM image, so `RV.step` executes `rvInstruction input`.
    - Decoder: the entry's data is `rvData input` (`rv_pooled_fields`, which also gives `rd ≠ x0` for loads); the
      query fixes the store/byte/sign selectors, PC limbs, immediate limbs and register indices (`rv_query_facts`).
    - Ports: all three ports read the pre-state (`rv_row_port_reads3`): rs1, then the aligned RAM cell (loads) or rs2
      (stores), then rd (loads) or the cell's old word (stores). Every port address is a public cell, so a RAM
      address is canonical and aligned (`RVNativeInputs.aligned`).
    - Address: `effective_address` (cell plus byte offset); halfwords have an even offset (`halfword_aligned`).
    - Loads (`RV.State.loadView`): RAM loads extend the read word's slice (`rv_ram_load_data`), ROM loads the public
      subword ROM table's word, the ROM image (`rv_rom_load_data`, `ROM.wordsRV`; the row history never changes it);
      `RV.exec_load_subword` reads the same slice. Stores: the circuit keeps the store in RAM
      (`subword_store_ram_writable`) and merges rs2's low bytes into the old word (`store_byte_encoding`), which is
      the RV byte store (`RV.exec_store_subword`). PC: `pc_successor`. -/

namespace Airbender.SubwordMemory.Proofs
open Arithmetic Trace Trace.Proofs

theorem rv_trace_soundness (laws : RVPooledLaws) : RVSoundnessClaim := by
  intro p _ hp inverse trace initial cells program assumptions input output w relation
  have : ClockLaws PooledFamily p := laws.clockLaws
  obtain ⟨⟨accepted, decoded, member⟩, mapping⟩ := relation
  have core := Verification.holds_of_sublist (accepted.constraints _ member)
    (List.sublist_append_left (importedConstraints trace.rom.subwordMemory) importedConstraintsTimestampLookups)
  change FlatOperation.ConstraintsHoldFlat (Verification.environment w)
    (importedConstraints trace.rom.subwordMemory) at core
  rw [assumptions.subwordTable] at core
  have active : w 4 = 1 := accepted.active _ member
  have limbSize : limbBase < p := by dsimp [limbBase]; omega
  have clockSize : 2 * timestampBase + 4 < p := by dsimp [timestampBase]; omega
  have arithmeticInverse : (-30720 : ZMod p) * 65536 = 1 := by
    calc
      (-30720 : ZMod p) * 65536 = (-3840 : ZMod p) * 524288 := by ring
      _ = 1 := inverse
  have oneValue : (1 : ZMod p).val = 1 := by
    simpa only [Nat.cast_one] using ZMod.val_natCast_of_lt (by omega : 1 < p)
  have image := assumptions.initialization.image
  obtain ⟨addresses, programImage⟩ := assumptions.initialization.programImage
  -- The row's program entry: its bytes decode to the row's instruction, and its data is `rvData input`.
  obtain ⟨entry, present, family, query, decodes⟩ := mapping.instruction
  obtain ⟨guard, bits, i, decodedI, projection⟩ := rvProgram_entry_fetch programImage entry present
  have hi : i = rvInstruction input := Option.some.inj (decodedI.symm.trans decodes)
  subst hi
  obtain ⟨loadNonzero, data⟩ := rv_pooled_fields projection family
  obtain ⟨selected, byteSelected, signSelected, pcWord, immediateWord, rs1Query, rs2Query, _⟩ :=
    rv_query_facts hp core data query
  -- Fetch/step: the row's pre-state is at the entry's PC and executes the entry's instruction.
  obtain ⟨beforePC, step⟩ := rv_step_of_position mapping.state (rv_query_pc limbSize query) guard
    (by rw [← bits]; exact decodes)
  -- PC successor.
  have rowPC : input.pc = Word.mk (w 0).val (w 1).val :=
    congrArg₂ Word.mk mapping.words.pcLo mapping.words.pcHi
  have pcBounds : input.pc.Bounded := by
    rw [rowPC, pcWord]
    exact Word.ofBitVec_bound entry.pc
  have pcNext := pc_successor (by omega) arithmeticInverse core
    ⟨by rw [rowPC]; exact (ZMod.natCast_zmod_val _).symm,
     by rw [rowPC]; exact (ZMod.natCast_zmod_val _).symm,
     mapping.words.finalPCLo, mapping.words.finalPCHi⟩ pcBounds
  have hpc : input.before.pc + 4 = output.pc.toBitVec := by
    rw [pcNext.2.2, rowPC, pcWord, Word.ofBitVec_roundtrip, beforePC]
  -- Operand words.
  have sourceWord : input.source = Word.mk (w 19).val (w 20).val :=
    congrArg₂ Word.mk mapping.words.sourceLo mapping.words.sourceHi
  have immediateIs : input.immediate = Word.mk (w 8).val (w 9).val :=
    congrArg₂ Word.mk mapping.words.immediateLo mapping.words.immediateHi
  have dataWord : output.data = Word.mk (w 33).val (w 34).val :=
    congrArg₂ Word.mk mapping.words.outputLo mapping.words.outputHi
  have cellWord : output.cell =
      Word.mk (if input.store then w 27 else w 21).val (if input.store then w 28 else w 22).val :=
    congrArg₂ Word.mk mapping.words.cellLo mapping.words.cellHi
  have offsetImmediate : input.encodedImmediate.signExtend 32 = (Word.mk (w 8).val (w 9).val).toBitVec := by
    rw [immediateWord, Word.ofBitVec_roundtrip]
  have immediateBound : (Word.mk (w 8).val (w 9).val).Bounded := by
    rw [immediateWord]
    exact Word.ofBitVec_bound _
  -- Port values are bounded words.
  have readBounds := (laws.valueBounds (by omega) inverse accepted
    assumptions.initialization.clocks image
    assumptions.wordTable assumptions.subwordTable programImage decoded).1 _ member
  have portBound (k : Fin 3) := readBounds importedConstraintsMemoryPorts[k]
    (by change importedConstraintsMemoryPorts[k] ∈ importedConstraintsMemoryPorts
        fin_cases k <;> simp [importedConstraintsMemoryPorts])
  have sourceBound : (Word.mk (w 19).val (w 20).val).Bounded := by
    simpa [read_word, importedConstraintsMemoryPorts] using portBound 0
  have readBound : (Word.mk (w 25).val (w 26).val).Bounded := by
    simpa [read_word, importedConstraintsMemoryPorts] using portBound 1
  have oldBound : (Word.mk (w 31).val (w 32).val).Bounded := by
    simpa [read_word, importedConstraintsMemoryPorts] using portBound 2
  -- The row's port reads in the pre-state.
  obtain ⟨_, _, _, _, _, _, _, current, _⟩ :=
    rv_pooled_row_history laws clockSize inverse accepted assumptions decoded mapping.state
  have shape : (⟨.subwordMemory, w⟩ : Row p PooledFamily).ports =
      #[importedConstraintsMemoryPorts[0], importedConstraintsMemoryPorts[1],
        importedConstraintsMemoryPorts[2]] := by
    have portsEq : (⟨.subwordMemory, w⟩ : Row p PooledFamily).ports = importedConstraintsMemoryPorts := by rfl
    rw [portsEq]
    rfl
  dsimp only [rowEvents] at current
  rw [shape] at current
  obtain ⟨⟨firstCell, _, firstAddress, firstRead⟩, ⟨secondCell, secondMember, secondAddress, secondRead⟩,
      ⟨thirdCell, thirdMember, thirdAddress, thirdRead⟩⟩ :=
    rv_row_port_reads3 trace.memoryEpoch (by simp [importedConstraintsMemoryPorts])
      (by simp [importedConstraintsMemoryPorts]) current
  have valueRs1 : (w 5).val = input.rs1.toNat := by
    rw [rs1Query, ZMod.val_natCast, Nat.mod_eq_of_lt (by have := input.rs1.isLt; omega)]
  have firstIs : firstCell = .register input.rs1 := cell_address_injective (by
    rw [firstAddress]
    simp [importedConstraintsMemoryPorts, MemoryAddress.code, Cell.addressCode, valueRs1])
  subst firstIs
  have sourceRead : input.before.getReg input.rs1 = input.source.toBitVec := by
    rw [readRV_register] at firstRead
    rw [Option.some.inj firstRead, sourceWord]
    simp [importedConstraintsMemoryPorts, MemoryPort.readCode, pairCode, memoryWord]
  have secondWord : memoryWord ((importedConstraintsMemoryPorts[1]).readCode w) =
      (Word.mk (w 25).val (w 26).val).toBitVec := by
    simp [importedConstraintsMemoryPorts, MemoryPort.readCode, pairCode, memoryWord]
  have thirdWord : memoryWord ((importedConstraintsMemoryPorts[2]).readCode w) =
      (Word.mk (w 31).val (w 32).val).toBitVec := by
    simp [importedConstraintsMemoryPorts, MemoryPort.readCode, pairCode, memoryWord]
  rw [secondWord] at secondRead
  rw [thirdWord] at thirdRead
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
      output.cell.toBitVec = a ∧
      output.cell.toBitVec.toNat = (input.source.toBitVec + input.immediate.toBitVec).toNat / 4 * 4 ∧
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
    have cellIsA : output.cell.toBitVec = a := by rw [cellWord, cellIs, Word.ofBitVec_roundtrip]
    have aligned : a.toNat % 4 = 0 := by
      have value := address.2.1
      rw [← Word.toBitVec_toNat (Word.ofBitVec_bound a), Word.ofBitVec_roundtrip] at value
      exact value
    have sum : input.source.toBitVec + input.immediate.toBitVec = a + BitVec.ofNat 32 offset := by
      rw [sourceWord, immediateIs]
      exact address.2.2.2.1.symm
    refine ⟨cellIsA, ?_, ?_⟩
    · rw [cellIsA, sum]
      have small := a.isLt
      have offsetSmall : offset < 4 := address.2.2.1
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]
      omega
    · rw [sourceRead, offsetImmediate, ← immediateIs, sum]
  cases hs : input.store
  · -- Loads: the second port reads the aligned RAM cell, ROM loads read the public subword ROM table.
    simp only [hs, Bool.false_eq_true, ite_false] at selected cellWord cellFacts ⊢
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
    have aligned : a.toNat % 4 = 0 := assumptions.initialization.aligned _ secondMember
    obtain ⟨cellIsA, addressFor, target⟩ := cellFacts a cellIs
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
        obtain ⟨_, _, middle, _, _, writes, atState⟩ := mapping.state
        have agree : input.before.rom = initial.rom := by
          rw [atState]
          exact (rvWriteHistory_rom writes : middle.rom = initial.rom)
        rw [RV.read_loadView_rom _ _ _ (by unfold RV.ROM_END at below ⊢; omega), agree, cellValue]
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
    refine ⟨addressFor, ?_⟩
    rw [step]
    simp only [rvInstruction, hs, Bool.false_eq_true, ite_false]
    rw [exec, dataWord]
    exact ⟨_, rfl, rv_same_of_write _ _ _ _ _ (fun _ => value.symm) hpc⟩
  · -- Stores: the second port reads rs2, the third reads and writes the aligned RAM cell.
    simp only [hs, ite_true] at selected cellWord cellFacts ⊢
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
    have aligned : a.toNat % 4 = 0 := assumptions.initialization.aligned _ thirdMember
    obtain ⟨cellIsA, addressFor, target⟩ := cellFacts a cellIs
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
    refine ⟨addressFor, ?_⟩
    rw [step]
    simp only [rvInstruction, hs, ite_true]
    rw [exec, cellIsA, dataWord]
    exact ⟨_, rfl, rv_same_of_store _ _ _ _ _ rfl hpc⟩

theorem babyBear_rv_trace_soundness (laws : RVPooledLaws) : BabyBearRVSoundnessClaim := by
  intro trace initial cells program assumptions input output w relation
  exact rv_trace_soundness laws (p := babyBearModulus) (by decide) (by decide) trace initial cells program
    assumptions input output w relation

end Airbender.SubwordMemory.Proofs
