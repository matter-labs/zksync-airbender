import Airbender.Proofs.AddSub.ModularSelectors
import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Proofs.AddSub.Modular
import Airbender.Proofs.AddSub.ModularProgram
import Airbender.Proofs.Trace.Arithmetic

namespace Airbender.AddSub.Modular.Proofs
open Arithmetic Trace Trace.Proofs Reference.RiscV.Sail Reference.Sail
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

def nativeInput (opcode : Opcode) (rs1 rs2 rd : BitVec 5)
    (w : Nat → ZMod babyBearModulus) (before : State) : Input :=
  ⟨opcode, (Word.mk (w 25).val (w 26).val).toBitVec,
    (Word.mk (w 29).val (w 30).val).toBitVec,
    (Word.mk (w 31).val (w 32).val).toBitVec,
    .Regidx rs1, .Regidx rs2, .Regidx rd, ⟨(w 0).val, (w 1).val⟩, before⟩

theorem word_residue (w : Nat → ZMod babyBearModulus) (lo hi : Nat)
    (bounds : (Word.mk (w lo).val (w hi).val).Bounded) :
    (((Word.mk (w lo).val (w hi).val).toBitVec.toNat) : ZMod babyBearModulus) =
      w lo + 65536 * w hi := by
  have small : (Word.mk (w lo).val (w hi).val).value < 2 ^ 32 := by
    dsimp [Word.Bounded, Word.value, limbBase] at *
    omega
  change (((Word.mk (w lo).val (w hi).val).value % 2 ^ 32 : Nat) : ZMod babyBearModulus) = _
  rw [Nat.mod_eq_of_lt small]
  simp [Word.value, limbBase]

/-- Recover the old destination from the third native port before its write,
    including when it aliases either source register. -/
theorem old_destination_read {p : Nat} (hp : FieldCapacity.NoWrap p limbBase)
    {w : Nat → ZMod p} {entry : ProgramEntry}
    (query : (⟨.addSub, w⟩ : Row p).decoderQuery = entry.query)
    {cells : List Cell} (epoch : Nat) {before after : State}
    (history : SailHistory cells (rowEvents epoch (⟨.addSub, w⟩ : Row p)).reverse before after) :
    run (SailRV32.Functions.rX_bits (.Regidx entry.data.rd)) before =
      .ok (Word.mk (w 31).val (w 32).val).toBitVec before := by
  have index := (query_register_indices hp query).2.2
  change (w 7).val = entry.data.rd.toNat at index
  have address : importedConstraintsMemoryPorts[2].address.code w =
      (Cell.register entry.data.rd).addressCode := by
    simpa [importedConstraintsMemoryPorts, MemoryAddress.code, Cell.addressCode] using
      congrArg (Nat.pair 0) index
  have read := row_history_read epoch history (port := importedConstraintsMemoryPorts[2])
    (by simp [Row.ports, importedConstraintsMemoryPorts]) address
  simpa [importedConstraintsMemoryPorts, MemoryPort.readCode, pairCode, memoryWord, Cell.read] using read

theorem native_interfaces
    {initial : State} {cells : List Cell} {seed : List (MemoryToken babyBearModulus)}
    (image : initialImage initial cells = some seed)
    (registers : ∀ index, Cell.register index ∈ cells)
    (setup : Table (ZMod babyBearModulus) (fields 9)) (epoch : Nat)
    {w : Nat → ZMod babyBearModulus}
    (constraints : FlatOperation.ConstraintsHoldFlat (Verification.environment w) clockConstraints)
    (active : w 4 = 1) {entry : ProgramEntry}
    (query : (⟨.addSub, w⟩ : Row babyBearModulus).decoderQuery = entry.query)
    (opcode : Opcode) (rs1 rs2 rd : BitVec 5)
    (data : entry.data = nativeData opcode rs1 rs2 rd)
    {before after : State} {events : List MemoryAccess}
    (past : SailHistory cells events initial before)
    (history : SailHistory cells (rowEvents epoch (⟨.addSub, w⟩ : Row babyBearModulus)).reverse before after)
    (pc : run (SailRV32.Functions.get_arch_pc ()) before =
      .ok (Word.mk (w 0).val (w 1).val).toBitVec before) :
    InterfaceAssumptions (nativeInput opcode rs1 rs2 rd w before)
      ⟨⟨(w 33).val, (w 34).val⟩, ⟨(w 19).val, (w 20).val⟩⟩ w := by
  have small : entry.data.mask < 512 := by
    rw [data]
    unfold nativeData arithmeticFields
    split
    · decide
    · change 2 ^ (opcode.selector - 10) < 512
      cases opcode <;> decide
  have flags := row_query_selectors_of_bound (p := babyBearModulus) (by decide)
    setup constraints small query
  change ∀ i : Fin 9, w #[10, 11, 12, 13, 14, 15, 16, 17, 18][i] =
    if entry.data.mask.testBit i.val then 1 else 0 at flags
  rw [data] at flags
  have left := row_history_source_read (p := babyBearModulus) (by decide) epoch history query
    (port := importedConstraintsMemoryPorts[0]) rfl
  simp [importedConstraintsMemoryPorts, MemoryPort.readCode, pairCode, memoryWord] at left
  have right := (addsub_history_registers (p := babyBearModulus) (by decide) query epoch history).1
  have old := old_destination_read (p := babyBearModulus) (by decide) query epoch history
  obtain ⟨leftValue, leftRead⟩ := image_register_after_history image past rs1 (registers rs1)
  obtain ⟨rightValue, rightRead⟩ := image_register_after_history image past rs2 (registers rs2)
  constructor
  · exact active
  · intro k lower upper
    have flag := flags ⟨k - 10, by omega⟩
    rw [native_mask_bit opcode rs1 rs2 rd k lower] at flag
    simpa [nativeInput, zeroRegister, native_selector_index k lower upper] using flag
  · have canonical := native_query_pc_word (p := babyBearModulus) (by decide) query
    change Word.mk (w 0).val (w 1).val = Word.ofBitVec entry.pc at canonical
    change (Word.mk (w 0).val (w 1).val).Bounded
    exact canonical.symm ▸ Word.ofBitVec_bound entry.pc
  · constructor
    · refine ⟨leftValue, leftRead, ?_⟩
      intro nonzero
      have nz : rd ≠ (0#5) := by
        intro zero
        apply nonzero
        simp [nativeInput, zero, zeroRegister]
      have index : entry.data.rs1 = rs1 := by
        rw [data]
        simp [nativeData, arithmeticFields, nz]
      rw [index] at left
      exact (EStateM.Result.ok.inj (leftRead.symm.trans left)).1
    · refine ⟨rightValue, rightRead, ?_⟩
      intro nonzero
      have nz : rd ≠ (0#5) := by
        intro zero
        apply nonzero
        simp [nativeInput, zero, zeroRegister]
      have index : entry.data.rs2 = rs2 := by
        rw [data]
        simp [nativeData, arithmeticFields, nz]
      rw [index] at right
      exact (EStateM.Result.ok.inj (rightRead.symm.trans right)).1
    · intro _ _
      simpa only [data, native_rd, nativeInput] using old
    · exact pc

theorem native_execution
    {initial : State} {cells : List Cell} {seed : List (MemoryToken babyBearModulus)}
    (image : initialImage initial cells = some seed)
    (registers : ∀ index, Cell.register index ∈ cells)
    (setup : Table (ZMod babyBearModulus) (fields 9)) (epoch : Nat)
    {w : Nat → ZMod babyBearModulus}
    (constraints : FlatOperation.ConstraintsHoldFlat (Verification.environment w) clockConstraints)
    (active : w 4 = 1)
    (bounds : (Word.mk (w 25).val (w 26).val).Bounded ∧
      (Word.mk (w 29).val (w 30).val).Bounded ∧ (Word.mk (w 31).val (w 32).val).Bounded)
    {entry : ProgramEntry}
    (query : (⟨.addSub, w⟩ : Row babyBearModulus).decoderQuery = entry.query)
    (opcode : Opcode) (rs1 rs2 rd : BitVec 5)
    (data : entry.data = nativeData opcode rs1 rs2 rd)
    {before after : State} {events : List MemoryAccess}
    (past : SailHistory cells events initial before)
    (history : SailHistory cells (rowEvents epoch (⟨.addSub, w⟩ : Row babyBearModulus)).reverse before after)
    (pc : run (SailRV32.Functions.get_arch_pc ()) before =
      .ok (Word.mk (w 0).val (w 1).val).toBitVec before) :
    run (normalStep (clause opcode rs1 rs2 rd)) before =
      .ok SailRV32.Functions.RETIRE_SUCCESS
        (retiredState after (Word.mk (w 19).val (w 20).val).toBitVec) := by
  let input := nativeInput opcode rs1 rs2 rd w before
  let output : Output := ⟨⟨(w 33).val, (w 34).val⟩, ⟨(w 19).val, (w 20).val⟩⟩
  have destination : entry.data.rd = rd := data ▸ native_rd opcode rs1 rs2 rd
  have index := (query_register_indices (p := babyBearModulus) (by decide) query).2.2
  have rdColumn : w 7 = (rd.toNat : ZMod babyBearModulus) := by
    change (w 7).val = entry.data.rd.toNat at index
    rw [destination] at index
    exact (ZMod.natCast_zmod_val (w 7)).symm.trans (congrArg Nat.cast index)
  have mapping : WordMapping input output w := by
    constructor
    · intro _; exact (word_residue w 25 26 bounds.1).symm
    · intro _; exact (word_residue w 29 30 bounds.2.1).symm
    · intro _ _; exact (word_residue w 31 32 bounds.2.2).symm
    · exact rdColumn
    · exact (ZMod.natCast_zmod_val _).symm
    · exact (ZMod.natCast_zmod_val _).symm
    · rfl
    · rfl
    · rfl
    · rfl
  have interfaces := native_interfaces image registers setup epoch constraints active query
    opcode rs1 rs2 rd data past history pc
  have core := Verification.holds_of_sublist constraints
    (List.sublist_append_left importedConstraints importedConstraintsTimestampLookups)
  obtain ⟨checkedAfter, normal, projected⟩ :=
    AddSub.Proofs.modular_soundness input output w ⟨interfaces, core, mapping⟩
  have written := (addsub_history_registers (p := babyBearModulus) (by decide) query epoch history).2
  rw [destination] at written
  have nativeProjection := projected_step_of_write rd output written
  have same := (EStateM.Result.ok.inj (projected.symm.trans nativeProjection)).2
  rw [same] at normal
  exact normal

end Airbender.AddSub.Modular.Proofs
