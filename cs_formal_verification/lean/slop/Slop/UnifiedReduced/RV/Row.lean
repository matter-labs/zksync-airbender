module
public import Human.Helpers.UnifiedReduced.RVProgram
public import Slop.UnifiedReduced.WordROM
public import Slop.UnifiedReduced.WordMemory
public import Slop.Trace.RVPorts
public import Slop.Trace.RVWritable
public import Slop.ISA.RV.Same
public import Slop.Trace.RVProgram
public import Slop.Trace.RVCells
public import Slop.Trace.DecoderBits
public import Slop.UnifiedReduced
public import Slop.JumpBranchSlt.RVDecoder
public import Slop.ShiftBinop.RVDecoder
public import Slop.CleanCore.Circuit.Operations
public import Slop.Defs.Helpers.Memory.Ports
public import Slop.Defs.Helpers.Memory.RowEvents

@[expose] public section

/-! Row-level facts of one unified row on the RV route: decoder selectors and field bounds of the RV table
    (`rvDecoderFields`), and the row's three ports read against an RV history (`rv_three_ports`): operand registers,
    destination register write, RAM store and RAM load. -/

namespace Airbender.UnifiedReduced.Proofs.RV
open Arithmetic Trace Trace.Proofs
set_option warningAsError true
set_option maxRecDepth 16384

theorem rv_decoder_selectors {p : Nat} [Fact p.Prime] (hp : 524288 < p)
    {setup : Table (ZMod p) (fields 10)} {w : Nat → ZMod p} {entry : RVProgramEntry}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (small : entry.data.mask < 524288) (query : decoderQuery w = entry.query) :
    ∀ i : Fin 19, w importedConstraintsDecoderColumns.flags[i] =
      if entry.data.mask.testBit i.val then 1 else 0 := by
  let bits (i : Fin 19) := w importedConstraintsDecoderColumns.flags[i]
  have boolean : ∀ i, bits i = 0 ∨ bits i = 1 := by
    intro i
    have flag := local_flags h ⟨i.val + 1, by omega⟩
    fin_cases i <;> simpa [bits, importedConstraintsDecoderColumns] using flag
  have packed := congrArg (fun q : Vector (ZMod p) 9 => q[8]) query
  change (∑ i : Fin 19, (2 ^ i.val : Nat) * bits i) = (entry.data.mask : ZMod p) at packed
  exact Trace.Proofs.unpack_decoder_bits_general (by simpa using hp)
    (by simpa using small) boolean packed

/-- The five branches of `rvDecoderFields`. -/
theorem rv_fields_cases {i : RV.Instr} {d : DecoderData UnifiedFamily}
    (fields : rvDecoderFields i = some d) :
    (rvNopWrite i = true ∧ d = rvNopFields) ∨
    (rvNopWrite i = false ∧ rvWordFields i = some d) ∨
    (rvNopWrite i = false ∧ rvWordFields i = none ∧
      ∃ j, JumpBranchSlt.rvDecoderFields i = some j ∧ d = jumpFields j) ∨
    (rvNopWrite i = false ∧ rvWordFields i = none ∧ JumpBranchSlt.rvDecoderFields i = none ∧
      ∃ j, ShiftBinop.rvDecoderFields i = some j ∧ d = binaryFields j) ∨
    (rvNopWrite i = false ∧ rvWordFields i = none ∧ JumpBranchSlt.rvDecoderFields i = none ∧
      ShiftBinop.rvDecoderFields i = none ∧ rvCustomFields i = some d) := by
  unfold rvDecoderFields at fields
  cases nop : rvNopWrite i
  · simp only [nop, Bool.false_eq_true, ↓reduceIte] at fields
    cases word : rvWordFields i with
    | some e =>
      rw [word] at fields
      obtain rfl : e = d := by simpa using fields
      exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    | none =>
      rw [word] at fields
      cases jump : JumpBranchSlt.rvDecoderFields i with
      | some j =>
        rw [jump] at fields
        obtain rfl : jumpFields j = d := by simpa using fields
        exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl, j, rfl, rfl⟩))
      | none =>
        rw [jump] at fields
        cases binary : ShiftBinop.rvDecoderFields i with
        | some j =>
          rw [binary] at fields
          obtain rfl : binaryFields j = d := by simpa using fields
          exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl, j, rfl, rfl⟩)))
        | none =>
          rw [binary] at fields
          exact Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl, rfl, by simpa using fields⟩)))
  · simp only [nop, ↓reduceIte, Option.some.injEq] at fields
    exact Or.inl ⟨rfl, fields.symm⟩

theorem rv_word_fields_bounds {i : RV.Instr} {d : DecoderData UnifiedFamily}
    (fields : rvWordFields i = some d) :
    d.immediate.Bounded ∧ (d.mask = 1 ∨ d.mask = 2 ∨ d.mask = 4 ∨ d.mask = 131072 ∨ d.mask = 262144) ∧
      d.funct3 = 0 := by
  unfold rvWordFields at fields
  split at fields
  all_goals first
    | (cases fields; done)
    | (obtain rfl := Option.some.inj fields
       first
         | exact ⟨Word.ofBitVec_bound _, by simp, rfl⟩
         | exact ⟨⟨by simp [limbBase], by simp [limbBase]⟩, by simp, rfl⟩)

theorem rv_custom_fields_bounds {i : RV.Instr} {d : DecoderData UnifiedFamily}
    (fields : rvCustomFields i = some d) :
    d.immediate.Bounded ∧ (d.mask = 512 ∨ d.mask = 65536) ∧ d.funct3 < 55 := by
  unfold rvCustomFields at fields
  split at fields
  · obtain rfl := Option.some.inj fields
    norm_num [Word.Bounded, limbBase]
  · rename_i n rd rs1
    cases found : customRotationTag n with
    | none => simp [found] at fields
    | some tag =>
      simp only [found, Option.map_some, Option.some.injEq] at fields
      subst d
      refine ⟨by norm_num [Word.Bounded, limbBase], Or.inr rfl, ?_⟩
      unfold customRotationTag at found
      split_ifs at found <;> cases found <;> norm_num
  · cases fields

theorem rv_field_bounds {i : RV.Instr} {d : DecoderData UnifiedFamily}
    (fields : rvDecoderFields i = some d) :
    d.immediate.Bounded ∧ d.mask < 524288 ∧ d.funct3 < 55 := by
  rcases rv_fields_cases fields with ⟨_, rfl⟩ | ⟨_, word⟩ | ⟨_, _, j, jump, rfl⟩ |
      ⟨_, _, _, j, binary, rfl⟩ | ⟨_, _, _, _, custom⟩
  · exact ⟨⟨by decide, by decide⟩, by decide, by decide⟩
  · obtain ⟨imm, mask, f3⟩ := rv_word_fields_bounds word
    refine ⟨imm, ?_, by omega⟩
    rcases mask with m | m | m | m | m <;> omega
  · have bounds := JumpBranchSlt.Proofs.rv_decoder_field_bounds jump
    change j.immediate.Bounded ∧ 1024 * j.mask < 524288 ∧ j.funct3 < 55
    exact ⟨bounds.1, by omega, by omega⟩
  · have bounds := ShiftBinop.Proofs.rv_decoder_field_bounds binary
    change j.immediate.Bounded ∧ 32768 * j.mask < 524288 ∧ _
    refine ⟨bounds.1, by omega, ?_⟩
    dsimp [binaryFields, Trace.DecoderData.mapFamily]
    split_ifs <;> omega
  · obtain ⟨imm, mask, f3⟩ := rv_custom_fields_bounds custom
    exact ⟨imm, by omega, f3⟩

/-! ### The row's ports against an RV history -/

theorem rv_row_ports {p : Nat} {cells : List Cell} {w : Nat → ZMod p} (epoch : Nat)
    {before after : RV.State}
    (history : RVHistory cells (rowEvents epoch (⟨.machine, w⟩ : Row p UnifiedFamily)).reverse before after) :
    ∃ c0 ∈ cells, ∃ c1 ∈ cells, ∃ c2 ∈ cells,
      c0.addressCode = Nat.pair 0 (Nat.pair (w 5).val 0) ∧
      c0.readRV before = some (Word.mk (w 36).val (w 37).val).toBitVec ∧
      c1.addressCode = Nat.pair (w 28).val (Nat.pair (w 38).val (w 39).val) ∧
      c1.readRV before = some (Word.mk (w 42).val (w 43).val).toBitVec ∧
      c2.addressCode = Nat.pair (w 29).val (Nat.pair (w 44).val (w 45).val) ∧
      c2.readRV before = some (Word.mk (w 48).val (w 49).val).toBitVec ∧
      c2.applyRV (Word.mk (w 50).val (w 51).val).toBitVec before = some after := by
  have shaped : RVHistory cells (nativeRowEvents epoch importedConstraintsTraceColumns
      #[importedConstraintsMemoryPorts[0], importedConstraintsMemoryPorts[1], importedConstraintsMemoryPorts[2]]
      w).reverse before after := history
  obtain ⟨c0, m0, c1, m1, c2, m2, a0, r0, a1, r1, a2, r2, w2⟩ :=
    rv_three_ports epoch (by simp [importedConstraintsMemoryPorts]) (by simp [importedConstraintsMemoryPorts])
      shaped
  refine ⟨c0, m0, c1, m1, c2, m2, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (simpa [importedConstraintsMemoryPorts, MemoryAddress.code, pairCode] using a0)
    | (simpa [importedConstraintsMemoryPorts, MemoryAddress.code, pairCode] using a1)
    | (simpa [importedConstraintsMemoryPorts, MemoryAddress.code, pairCode] using a2)
    | (simpa [importedConstraintsMemoryPorts, MemoryPort.readCode, MemoryPort.writeCode, WordColumns.code,
        pairCode, memoryWord] using r0)
    | (simpa [importedConstraintsMemoryPorts, MemoryPort.readCode, MemoryPort.writeCode, WordColumns.code,
        pairCode, memoryWord] using r1)
    | (simpa [importedConstraintsMemoryPorts, MemoryPort.readCode, MemoryPort.writeCode, WordColumns.code,
        pairCode, memoryWord] using r2)
    | (simpa [importedConstraintsMemoryPorts, MemoryPort.readCode, MemoryPort.writeCode, WordColumns.code,
        pairCode, memoryWord] using w2)

private theorem register_cell {cell : Cell} {index : BitVec 5} {p : Nat} {column : ZMod p}
    (code : cell.addressCode = Nat.pair 0 (Nat.pair column.val 0)) (value : column.val = index.toNat) :
    cell = .register index := by
  apply cell_address_injective
  rw [code, value]
  rfl

/-- The operand ports of a row that does not load from RAM read the pre-state registers `rs1` and `rs2`. -/
theorem rv_register_reads {p : Nat} [Fact p.Prime] (hp : limbBase < p)
    {setup : Table (ZMod p) (fields 10)} {w : Nat → ZMod p} {entry : RVProgramEntry}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (noRAM : w 28 = 0) (query : decoderQuery w = entry.query)
    {cells : List Cell} (epoch : Nat) {before after : RV.State}
    (history : RVHistory cells (rowEvents epoch (⟨.machine, w⟩ : Row p UnifiedFamily)).reverse before after) :
    before.getReg entry.data.rs1 = (Word.mk (w 36).val (w 37).val).toBitVec ∧
      before.getReg entry.data.rs2 = (Word.mk (w 42).val (w 43).val).toBitVec := by
  have indices := rv_native_query_indices hp query
  change (w 5).val = entry.data.rs1.toNat ∧ (w 6).val = entry.data.rs2.toNat ∧ (w 7).val = entry.data.rd.toNat
    at indices
  have low := Verification.assertion_of_holds h ⟨26, by rw [constraint_count]; decide⟩
  have high := Verification.assertion_of_holds h ⟨27, by rw [constraint_count]; decide⟩
  op_index at low high
  simp [Expression.eval, Verification.environment, noRAM] at low high
  have location : w 38 = w 6 := by linear_combination low
  have upper : w 39 = 0 := by linear_combination high
  obtain ⟨c0, _, c1, _, _, _, a0, r0, a1, r1, _⟩ := rv_row_ports epoch history
  have e0 := register_cell a0 indices.1
  rw [noRAM, location, upper] at a1
  have e1 := register_cell (column := w 6) (by simpa using a1) indices.2.1
  subst e0 e1
  rw [readRV_register] at r0 r1
  exact ⟨Option.some.inj r0, Option.some.inj r1⟩

/-- The destination port of a row that does not store to RAM writes register `rd`: the pre-state's `rd` is the
    port's read value, and the post-state agrees with the pre-state with `rd` set to the written value. -/
theorem rv_register_write {p : Nat} [Fact p.Prime]
    {setup : Table (ZMod p) (fields 10)} {w : Nat → ZMod p} {rd : BitVec 5}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (noStore : w 29 = 0) (index : (w 7).val = rd.toNat)
    {cells : List Cell} (epoch : Nat) {before after : RV.State}
    (history : RVHistory cells (rowEvents epoch (⟨.machine, w⟩ : Row p UnifiedFamily)).reverse before after) :
    before.getReg rd = (Word.mk (w 48).val (w 49).val).toBitVec ∧
      RV.Same after (before.setReg rd (Word.mk (w 50).val (w 51).val).toBitVec) := by
  have low := Verification.assertion_of_holds h ⟨28, by rw [constraint_count]; decide⟩
  have high := Verification.assertion_of_holds h ⟨29, by rw [constraint_count]; decide⟩
  op_index at low high
  simp [Expression.eval, Verification.environment, noStore] at low high
  have location : w 44 = w 7 := by linear_combination low
  have upper : w 45 = 0 := by linear_combination high
  obtain ⟨_, _, _, _, c2, _, _, _, _, _, a2, r2, w2⟩ := rv_row_ports epoch history
  rw [noStore, location, upper] at a2
  have e2 := register_cell (column := w 7) (by simpa using a2) index
  subst e2
  rw [readRV_register] at r2
  refine ⟨Option.some.inj r2, ?_⟩
  unfold Cell.applyRV at w2
  split at w2
  · rename_i same
    obtain rfl := Option.some.inj w2
    exact RV.Same.symm (writeRV_self_same_register same (writeRV_register rd _ before))
  · rw [writeRV_register] at w2
    obtain rfl := Option.some.inj w2
    exact RV.Same.refl _

/-- The destination port of a store row writes the RAM word at its address limbs; the address is a tracked cell, so
    it is aligned, and the circuit keeps it out of ROM. -/
theorem rv_store_write {p : Nat} [Fact p.Prime] (hp : 131072 < p)
    {setup : Table (ZMod p) (fields 10)} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (load : w 28 = 0) (store : w 29 = 1)
    {cells : List Cell} (aligned : ∀ cell ∈ cells, cell.Aligned) (epoch : Nat) {before after : RV.State}
    (history : RVHistory cells (rowEvents epoch (⟨.machine, w⟩ : Row p UnifiedFamily)).reverse before after) :
    (Word.mk (w 44).val (w 45).val).Bounded ∧
      (Word.mk (w 44).val (w 45).val).toBitVec.toNat % 4 = 0 ∧
      RV.writable (Word.mk (w 44).val (w 45).val).toBitVec 4 ∧
      RV.Same after (before.store (Word.mk (w 44).val (w 45).val).toBitVec
        (Word.mk (w 50).val (w 51).val).toBitVec 4) := by
  obtain ⟨_, _, _, _, c2, m2, _, _, _, _, a2, r2, w2⟩ := rv_row_ports epoch history
  have one : (w 29).val = 1 := by rw [store]; exact ZMod.val_one_eq_one_mod p ▸ Nat.mod_eq_of_lt (by omega)
  rw [one] at a2
  have high := (word_rom_selection hp true h (by simpa using load) (by simpa using store)).2 rfl
  cases c2 with
  | register index => simp [Cell.addressCode, Nat.pair_eq_pair] at a2
  | ram address =>
    have limbs : Word.ofBitVec address = Word.mk (w 44).val (w 45).val := by
      simp only [Cell.addressCode, Nat.pair_eq_pair] at a2
      exact congrArg₂ Word.mk a2.2.1 a2.2.2
    have bound : (Word.mk (w 44).val (w 45).val).Bounded := limbs ▸ Word.ofBitVec_bound address
    have same : (Word.mk (w 44).val (w 45).val).toBitVec = address := by
      rw [← limbs, Word.ofBitVec_roundtrip]
    rw [same]
    have isAligned : address.toNat % 4 = 0 := aligned _ m2
    have romHigh : 64 ≤ (Word.ofBitVec address).hi := by rw [limbs]; exact high
    have writable : RV.writable address 4 := by
      refine ⟨RVWritable.ram_index_rom_bound address romHigh, ?_⟩
      have := address.isLt
      unfold RV.RAM_END
      omega
    refine ⟨bound, isAligned, writable, ?_⟩
    unfold Cell.applyRV at w2
    split at w2
    · rename_i read
      obtain rfl := Option.some.inj w2
      rw [readRV_ram _ writable.2] at read
      have value := Option.some.inj read
      refine ⟨rfl, fun _ => rfl, rfl, ?_, rfl⟩
      simp only [RV.State.store, ← value, rv_write_read_self]
    · rw [writeRV_ram] at w2
      obtain rfl := Option.some.inj w2
      exact RV.Same.refl _

/-- The second port of a load row reads the RAM word at its address limbs, a tracked (so aligned, readable) cell. -/
theorem rv_load_read {p : Nat} [Fact p.Prime] {w : Nat → ZMod p} (load : w 28 = 1)
    {cells : List Cell} (aligned : ∀ cell ∈ cells, cell.Aligned) (epoch : Nat) {before after : RV.State}
    (history : RVHistory cells (rowEvents epoch (⟨.machine, w⟩ : Row p UnifiedFamily)).reverse before after) :
    (Word.mk (w 38).val (w 39).val).Bounded ∧
      (Word.mk (w 38).val (w 39).val).toBitVec.toNat % 4 = 0 ∧
      RV.readable (Word.mk (w 38).val (w 39).val).toBitVec 4 ∧
      RV.read before.mem (Word.mk (w 38).val (w 39).val).toBitVec 4 = (Word.mk (w 42).val (w 43).val).toBitVec := by
  obtain ⟨_, _, c1, m1, _, _, _, _, a1, r1, _⟩ := rv_row_ports epoch history
  have one : (w 28).val = 1 := by
    rw [load]; exact ZMod.val_one_eq_one_mod p ▸ Nat.mod_eq_of_lt (Fact.out : Nat.Prime p).one_lt
  rw [one] at a1
  cases c1 with
  | register index => simp [Cell.addressCode, Nat.pair_eq_pair] at a1
  | ram address =>
    have limbs : Word.ofBitVec address = Word.mk (w 38).val (w 39).val := by
      simp only [Cell.addressCode, Nat.pair_eq_pair] at a1
      exact congrArg₂ Word.mk a1.2.1 a1.2.2
    have bound : (Word.mk (w 38).val (w 39).val).Bounded := limbs ▸ Word.ofBitVec_bound address
    have same : (Word.mk (w 38).val (w 39).val).toBitVec = address := by
      rw [← limbs, Word.ofBitVec_roundtrip]
    rw [same]
    have readable := readable_of_readRV r1
    rw [readRV_ram _ readable] at r1
    exact ⟨bound, aligned _ m1, readable, Option.some.inj r1⟩

/-- A row whose destination register gets `value` and whose PC advances by four is the step `setReg` then
    `nextInstr`. -/
theorem rv_register_next {before after : RV.State} {rd : RV.Reg} {value final : RV.Word}
    (same : RV.Same after (before.setReg rd value)) (pc : final = before.pc + 4) :
    RV.Same (before.setReg rd value).nextInstr { after with pc := final } :=
  ⟨by simp [RV.State.nextInstr, RV.State.setReg, pc], fun i => (same.2.1 i).symm, same.2.2.1.symm,
    same.2.2.2.1.symm, same.2.2.2.2.symm⟩

end Airbender.UnifiedReduced.Proofs.RV
