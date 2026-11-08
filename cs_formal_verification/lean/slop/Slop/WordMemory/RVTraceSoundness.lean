module
public import Human.Circuits.WordMemory.RVTheorems
public import Slop.WordMemory
public import Slop.WordMemory.RVQuery
public import Slop.Trace.RVValues
public import Slop.Trace.RVRomRead
public import Slop.Trace.RVPooledRow
public import Slop.Trace.RVRowGlue
public import Slop.WordMemory.RVWritable

@[expose] public section

/-! RV32 LW/SW soundness (`RVSoundnessClaim`), on the RV route: no Sail state, interpreter, `Configured` or
    `OrdinaryWordAddress` fact.

    - Fetch/step: the row's program entry is an aligned word of the ROM image (`rvProgram_entry_fetch`);
      the row's pre-state has the entry's PC and the same ROM image, so `RV.step` executes `rvInstruction input`.
    - Decoder: the entry's data is `rvData input` (`rv_word_fields`, which also gives `rd ≠ x0` for LW); the query
      fixes the store selector, PC limbs, immediate limbs and register indices (`rv_query_facts`).
    - Ports: the row's first two ports read the pre-state (`rv_row_port_reads`): rs1, then the RAM word (LW) or rs2
      (SW). Every port address is a public cell (`rv_initialized_cells`), so a RAM address is canonical and aligned
      (`RVNativeInputs.aligned`).
    - Address: `effective_address`. LW data (`RV.State.loadView`): RAM (`ram_data`: the read word) or ROM
      (`rom_data`: the public ROM table, which holds the ROM image, `rv_rom_read`; the row history never changes
      the ROM image, `rvWriteHistory_rom`). SW: the circuit keeps the store in RAM (`word_store_ram_writable`) and stores the rs2
      word (`ram_data`). PC: `pc_successor`. -/

namespace Airbender.WordMemory.Proofs
open Arithmetic Trace Trace.Proofs

/-- The first two ports of a three-port row whose first port is read-only both read the row's pre-state: each reads
    a public cell at its address. -/
theorem rv_row_port_reads {p : Nat} {cells : List Cell} {columns : TraceColumns}
    {first second destination : MemoryPort} {w : Nat → ZMod p} (epoch : Nat)
    (firstReadonly : first.writeValue = none)
    {before after : RV.State}
    (history : RVHistory cells
      (nativeRowEvents epoch columns #[first, second, destination] w).reverse before after) :
    (∃ cell ∈ cells, cell.addressCode = first.address.code w ∧
      cell.readRV before = some (memoryWord (first.readCode w))) ∧
    (∃ cell ∈ cells, cell.addressCode = second.address.code w ∧
      cell.readRV before = some (memoryWord (second.readCode w))) := by
  have readonly : first.readCode w = first.writeCode w := by
    simp [MemoryPort.readCode, MemoryPort.writeCode, firstReadonly]
  dsimp [nativeRowEvents] at history
  cases history with
  | cons past destinationCell dm da dr dw =>
    cases past with
    | cons past rightCell rm ra rr rw =>
      cases past with
      | cons empty leftCell lm la lr lw =>
        cases empty with
        | nil =>
          have lr' : leftCell.readRV before = some (memoryWord (first.readCode w)) := lr
          have unchanged : leftCell.applyRV (memoryWord (first.writeCode w)) before = some before := by
            rw [← readonly]
            simp [Cell.applyRV, lr']
          have hm := Option.some.inj (lw.symm.trans unchanged)
          subst hm
          exact ⟨⟨leftCell, lm, la, lr'⟩, ⟨rightCell, rm, ra, rr⟩⟩

/-- A word below `ROM_END` at an aligned address: limb form. -/
private theorem rom_address (a : BitVec 32) (high : (Word.ofBitVec a).hi < 64) : a.toNat < RV.ROM_END := by
  unfold RV.ROM_END
  dsimp [Word.ofBitVec, limbBase] at high
  omega

theorem rv_trace_soundness (laws : RVPooledLaws) : RVSoundnessClaim := by
  intro p _ hp inverse trace initial cells program assumptions input output w relation
  have : ClockLaws PooledFamily p := laws.clockLaws
  obtain ⟨⟨accepted, decoded, member⟩, mapping⟩ := relation
  have core := Verification.holds_of_sublist (accepted.constraints _ member)
    (List.sublist_append_left (importedConstraints trace.rom.wordMemory) importedConstraintsTimestampLookups)
  have limbSize : limbBase < p := by dsimp [limbBase]; omega
  have clockSize : 2 * timestampBase + 4 < p := by dsimp [timestampBase]; omega
  have arithmeticInverse : (-30720 : ZMod p) * 65536 = 1 := by
    calc
      (-30720 : ZMod p) * 65536 = (-3840 : ZMod p) * 524288 := by ring
      _ = 1 := inverse
  have image := assumptions.initialization.image
  obtain ⟨addresses, programImage⟩ := assumptions.initialization.programImage
  -- The row's program entry: its bytes decode to the row's instruction, and its data is `rvData input`.
  obtain ⟨entry, present, family, query, decodes⟩ := mapping.instruction
  obtain ⟨guard, bits, i, decodedI, projection⟩ := rvProgram_entry_fetch programImage entry present
  have hi : i = rvInstruction input := Option.some.inj (decodedI.symm.trans decodes)
  subst hi
  obtain ⟨loadNonzero, data⟩ := rv_word_fields projection family
  obtain ⟨selected, pcWord, immediateWord, rs1Query, rs2Query, _⟩ := rv_query_facts hp data query
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
  have sourceWord : input.source = Word.mk (w 17).val (w 18).val :=
    congrArg₂ Word.mk mapping.words.sourceLo mapping.words.sourceHi
  have immediateIs : input.immediate = Word.mk (w 8).val (w 9).val :=
    congrArg₂ Word.mk mapping.words.immediateLo mapping.words.immediateHi
  have dataWord : output.data = Word.mk (w 31).val (w 32).val :=
    congrArg₂ Word.mk mapping.words.outputLo mapping.words.outputHi
  have addressWord : output.address =
      Word.mk (w (if input.store then 25 else 19)).val (w (if input.store then 26 else 20)).val :=
    congrArg₂ Word.mk mapping.words.addressLo mapping.words.addressHi
  have offset : input.encodedImmediate.signExtend 32 = (Word.mk (w 8).val (w 9).val).toBitVec := by
    rw [immediateWord, Word.ofBitVec_roundtrip]
  have immediateBound : (Word.mk (w 8).val (w 9).val).Bounded := by
    rw [immediateWord]
    exact Word.ofBitVec_bound _
  have readBounds := (laws.valueBounds (by omega) inverse accepted
    assumptions.initialization.clocks image
    assumptions.wordTable assumptions.subwordTable programImage decoded).1 _ member
  have sourceBound : (Word.mk (w 17).val (w 18).val).Bounded := by
    have source := readBounds importedConstraintsMemoryPorts[0]
      (by change importedConstraintsMemoryPorts[0] ∈ importedConstraintsMemoryPorts
          simp [importedConstraintsMemoryPorts])
    simpa [read_word, importedConstraintsMemoryPorts] using source
  -- The row's port reads in the pre-state.
  obtain ⟨_, _, _, _, _, _, _, current, _⟩ :=
    rv_pooled_row_history laws clockSize inverse accepted assumptions decoded mapping.state
  have shape : (⟨.wordMemory, w⟩ : Row p PooledFamily).ports =
      #[importedConstraintsMemoryPorts[0], importedConstraintsMemoryPorts[1],
        importedConstraintsMemoryPorts[2]] := by
    have portsEq : (⟨.wordMemory, w⟩ : Row p PooledFamily).ports = importedConstraintsMemoryPorts := by rfl
    rw [portsEq]
    rfl
  dsimp only [rowEvents] at current
  rw [shape] at current
  obtain ⟨⟨firstCell, _, firstAddress, firstRead⟩, ⟨secondCell, secondMember, secondAddress, secondRead⟩⟩ :=
    rv_row_port_reads trace.memoryEpoch (by simp [importedConstraintsMemoryPorts]) current
  have boundP : 32 ≤ p := by omega
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
      (Word.mk (w 23).val (w 24).val).toBitVec := by
    simp [importedConstraintsMemoryPorts, MemoryPort.readCode, pairCode, memoryWord]
  rw [secondWord] at secondRead
  have disabled : ∀ query, trace.rom.wordMemory.Contains #[] query → query[8] = 0 →
      query[1] = 0 ∧ query[2] = 0 := by
    intro query contains inactive
    exact Trace.RVValues.rv_rom_disabled (by omega) (by rwa [assumptions.wordTable] at contains) inactive
  have oneValue : (1 : ZMod p).val = 1 := by
    simpa only [Nat.cast_one] using ZMod.val_natCast_of_lt (by omega : 1 < p)
  cases hs : input.store
  · -- LW: the second port reads the RAM cell at the effective address.
    simp only [hs, Bool.false_eq_true, ite_false] at selected addressWord ⊢
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
    have aligned : a.toNat % 4 = 0 := assumptions.initialization.aligned _ secondMember
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
    -- The loaded word: RAM copies the read word; ROM reads the public starting bytes.
    have value : RV.read input.before.loadView a 4 = (Word.mk (w 31).val (w 32).val).toBitVec := by
      by_cases inROM : (w 20).val < 64
      · have flag : w 35 = 1 := by simpa [inROM] using classified.1
        have lookup := rom_data core selected (accepted.active _ member) flag
        rw [assumptions.wordTable] at lookup
        have rom := Trace.RVValues.rv_rom_read (by dsimp [ROM.limit]; omega)
          ⟨(w 19).val, (w 20).val⟩ (w 31) (w 32) addressBound inROM
          (by simpa only [ZMod.natCast_zmod_val] using lookup)
        rw [cellWord, Word.ofBitVec_roundtrip] at rom
        obtain ⟨_, _, middle, _, _, writes, atState⟩ := mapping.state
        have agree : input.before.rom = initial.rom := by
          rw [atState]
          exact (rvWriteHistory_rom writes : middle.rom = initial.rom)
        have below : a.toNat < RV.ROM_END := rom_address a (by rw [← hiEq]; exact inROM)
        rw [RV.read_loadView_rom _ _ _ (by unfold RV.ROM_END at below ⊢; omega), agree]
        exact rom.2
      · have flag : w 35 = 0 := by simpa [inROM] using classified.1
        have copied := ram_data disabled false core (by simpa using selected) flag
        change w 31 = w 23 ∧ w 32 = w 24 at copied
        have high : RV.ROM_END ≤ a.toNat := RVWritable.ram_index_rom_bound a (by rw [← hiEq]; omega)
        rw [RV.read_loadView_ram _ _ _ high (by have := a.isLt; omega), ramRead, copied.1, copied.2]
    refine ⟨by rw [addressWord, sourceWord, immediateIs, cellWord, Word.ofBitVec_roundtrip, address], ?_⟩
    have target : input.before.getReg input.rs1 + input.encodedImmediate.signExtend 32 = a := by
      rw [sourceRead, sourceWord, offset, address]
    refine ⟨(input.before.setReg input.rd (RV.read input.before.loadView a 4)).nextInstr, ?_, ?_⟩
    · rw [step]
      simp only [rvInstruction, hs, Bool.false_eq_true, ite_false, RV.exec, target, rd0]
      rw [ite_eq_left ⟨aligned, readable⟩]
      simp
    · rw [dataWord]
      exact rv_same_of_write _ _ _ _ _ (fun _ => value) hpc
  · -- SW: the second port reads rs2; the third writes the RAM cell at the effective address.
    simp only [hs, ite_true] at selected addressWord ⊢
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
    obtain ⟨cell, cellMember, cellAddress⟩ := rv_initialized_cells clockSize inverse accepted
      assumptions.initialization.clocks image _ member importedConstraintsMemoryPorts[2]
      (by change importedConstraintsMemoryPorts[2] ∈ importedConstraintsMemoryPorts
          simp [importedConstraintsMemoryPorts])
    cases cell with
    | register j =>
      simp [importedConstraintsMemoryPorts, MemoryAddress.code, Cell.addressCode, selected, pairCode,
        oneValue] at cellAddress
    | ram a =>
    have tagged : Nat.pair 1 (Nat.pair (w 25).val (w 26).val) = (Cell.ram a).addressCode := by
      rw [← cellAddress]
      simp [importedConstraintsMemoryPorts, MemoryAddress.code, selected, pairCode, oneValue]
    obtain ⟨_, loEq, hiEq⟩ := RVWritable.ram_code_limbs a 1 (w 25) (w 26) tagged
    have cellWord : Word.mk (w 25).val (w 26).val = Word.ofBitVec a := by rw [loEq, hiEq]
    have addressBound : (Word.mk (w 25).val (w 26).val).Bounded := cellWord ▸ Word.ofBitVec_bound a
    have aligned : a.toNat % 4 = 0 := assumptions.initialization.aligned _ cellMember
    have ram := RVWritable.word_store_ram_writable (by omega) trace.rom.wordMemory w core a cellAddress
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
    refine ⟨by rw [addressWord, sourceWord, immediateIs, cellWord, Word.ofBitVec_roundtrip, address], ?_⟩
    have target : input.before.getReg input.rs1 + input.encodedImmediate.signExtend 32 = a := by
      rw [sourceRead, sourceWord, offset, address]
    refine ⟨(input.before.store a (input.before.getReg input.rs2) 4).nextInstr, ?_, ?_⟩
    · rw [step]
      simp only [rvInstruction, hs, ite_true, RV.exec, target]
      rw [ite_eq_left ⟨aligned, writable⟩]
    · rw [dataWord, addressWord, cellWord, Word.ofBitVec_roundtrip]
      exact rv_same_of_store _ _ _ _ _ value hpc

theorem babyBear_rv_trace_soundness (laws : RVPooledLaws) : BabyBearRVSoundnessClaim := by
  intro trace initial cells program assumptions input output w relation
  exact rv_trace_soundness laws (p := babyBearModulus) (by decide) (by decide) trace initial cells program
    assumptions input output w relation

end Airbender.WordMemory.Proofs
