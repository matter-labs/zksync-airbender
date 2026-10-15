import Airbender.Proofs.UnifiedReduced.ModularDecoder
import Airbender.Proofs.AddSub.ModularNative
import Airbender.Proofs.UnifiedReduced.TriAddNative

namespace Airbender.UnifiedReduced.Modular.Proofs
open Arithmetic Trace Trace.Proofs Reference.RiscV.Sail Reference.Sail
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

/-- Name the standalone calculation's variables with the actual unified columns. -/
def lift (w : Nat → ZMod babyBearModulus) : Nat → ZMod babyBearModulus
  | 10 => w 11 | 11 => w 12 | 12 => w 13 | 13 => w 14 | 14 => w 15
  | 15 => w 16 | 16 => w 17 | 17 => w 18 | 18 => w 19
  | 19 => w 30 | 20 => w 31 | 21 => w 32 | 22 => w 33
  | 23 => w 34 | 24 => w 35 | 25 => w 36 | 26 => w 37
  | 27 => w 40 | 28 => w 41 | 29 => w 42 | 30 => w 43
  | 31 => w 48 | 32 => w 49 | 33 => w 50 | 34 => w 51
  | 35 => w 46 | 36 => w 47 | 37 => w 78 | 38 => w 79
  | 39 => w 53 | 40 => w 52 | 41 => w 80
  | 42 => w 131 | 43 => w 132 | 44 => w 133
  | i => w i

theorem canonical_output {setup : Table (ZMod babyBearModulus) (fields 10)}
    {w : Nat → ZMod babyBearModulus}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (s11 : w 11 = 0) (s12 : w 12 = 0) (s13 : w 13 = 0) (s20 : w 20 = 0)
    (selected : w 14 + w 15 + w 16 + w 17 = 1) :
    (w 50).val + 65536 * (w 51).val < babyBearModulus := by
  have borrow := Verification.assertion_of_holds h ⟨3, by rw [UnifiedReduced.constraint_count]; decide⟩
  have low := Verification.assertion_of_holds h ⟨4, by rw [UnifiedReduced.constraint_count]; decide⟩
  have high := Verification.assertion_of_holds h ⟨5, by rw [UnifiedReduced.constraint_count]; decide⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval,
    Verification.environment, s11, s12, s13, s20, selected] at borrow low high
  have b : w 52 = 1 := by linear_combination -borrow
  have boolean : w 53 * (w 53 - 1) = 0 := by
    rcases UnifiedReduced.Proofs.local_flags h 21 with zero | one
    · simp only [show w 53 = 0 from zero, zero_mul]
    · simp only [show w 53 = 1 from one, sub_self, mul_zero]
  obtain ⟨c, cb, hc⟩ := boolean_nat boolean
  have rlo := Verification.range16_bound (Verification.lookup_of_holds h
    ⟨0, by rw [UnifiedReduced.lookup_count]; decide⟩)
  have rhi := Verification.range16_bound (Verification.lookup_of_holds h
    ⟨1, by rw [UnifiedReduced.lookup_count]; decide⟩)
  have olo := Verification.range16_bound (Verification.lookup_of_holds h
    ⟨2, by rw [UnifiedReduced.lookup_count]; decide⟩)
  have ohi := Verification.range16_bound (Verification.lookup_of_holds h
    ⟨3, by rw [UnifiedReduced.lookup_count]; decide⟩)
  simp [Expression.eval, Verification.environment] at rlo rhi olo ohi
  have lowEq : (((w 78).val : Nat) : ZMod babyBearModulus) + 1 =
      (w 50).val + 65536 * c := by
    simp only [ZMod.natCast_zmod_val]
    rw [hc] at low
    linear_combination low
  have highEq : (c : ZMod babyBearModulus) + (w 79).val + 30720 = (w 51).val + 65536 := by
    simp only [ZMod.natCast_zmod_val]
    rw [hc, b] at high
    linear_combination high
  exact Word.lt_of_borrow (p := babyBearModulus) (output := ⟨(w 50).val, (w 51).val⟩)
    (remainder := ⟨(w 78).val, (w 79).val⟩) (modulus := ⟨1, 30720⟩)
    (by decide) ⟨olo, ohi⟩ ⟨by decide, by decide⟩ ⟨rlo, rhi⟩ cb
    (by simpa using lowEq) (by simpa using highEq)

theorem interfaces_from_history
    {initial : State} {cells : List Cell} {seed : List (MemoryToken babyBearModulus)}
    (image : initialImage initial cells = some seed) (registers : ∀ index, Cell.register index ∈ cells)
    {setup : Table (ZMod babyBearModulus) (fields 10)} {w : Nat → ZMod babyBearModulus}
    (core : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (active : w 4 = 1) {entry : ProgramEntry}
    (fields : mopDecoderFields entry.instruction = some entry.data) (query : decoderQuery w = entry.query)
    (opcode : AddSub.Modular.Opcode) (rs1 rs2 rd : BitVec 5)
    (encoding : entry.instruction = AddSub.Modular.instruction opcode rs1 rs2 rd)
    (epoch : Nat) {before after : State} {events : List MemoryAccess}
    (past : SailHistory cells events initial before)
    (history : SailHistory cells (rowEvents epoch (⟨.machine, w⟩ : Row babyBearModulus UnifiedFamily)).reverse before after)
    (pc : run (SailRV32.Functions.get_arch_pc ()) before = .ok (Control.initialPC w).toBitVec before) :
    AddSub.Modular.InterfaceAssumptions
      (AddSub.Modular.Proofs.nativeInput opcode rs1 rs2 rd (lift w) before)
      ⟨Control.destination w, Control.finalPC w⟩ (lift w) := by
  have data := mop_metadata opcode rs1 rs2 rd fields encoding
  have flags := UnifiedReduced.Proofs.decoder_selectors (p := babyBearModulus) (by decide)
    core (mop_bounds fields).2.1 query
  have disabled (i : Fin 12) : w importedConstraintsDecoderColumns.flags[(⟨7 + i.val, by omega⟩ : Fin 19)] = 0 := by
    have flag := flags ⟨7 + i.val, by omega⟩
    rw [data, mop_high_flags opcode rs1 rs2 rd i] at flag
    exact flag
  have noRead : w 28 = 0 := disabled 10
  have noWrite : w 29 = 0 := disabled 11
  have reads := UnifiedReduced.Proofs.register_reads (p := babyBearModulus) (by decide) core noRead query epoch history
  have old := UnifiedReduced.Proofs.triadd_old_read (p := babyBearModulus) (by decide) core noWrite query epoch history
  obtain ⟨leftValue, leftRead⟩ := image_register_after_history image past rs1 (registers rs1)
  obtain ⟨rightValue, rightRead⟩ := image_register_after_history image past rs2 (registers rs2)
  constructor
  · exact active
  · intro k lower upper
    have flag := flags ⟨k - 10, by omega⟩
    rw [data] at flag
    interval_cases k <;> cases opcode <;> by_cases zero : rd = (0#5)
    all_goals simpa [lift, AddSub.Modular.Proofs.nativeInput, mopData, DecoderData.mapFamily,
      AddSub.Modular.nativeData, Trace.arithmeticFields, zero, zeroRegister,
      AddSub.Modular.Opcode.selector, importedConstraintsDecoderColumns,
      Nat.testBit, Nat.shiftRight_eq_div_pow] using flag
  · have value := native_query_pc_word (p := babyBearModulus) (by decide) query
    change Control.initialPC w = Word.ofBitVec entry.pc at value
    change (Control.initialPC w).Bounded
    exact value.symm ▸ Word.ofBitVec_bound entry.pc
  · constructor
    · refine ⟨leftValue, leftRead, ?_⟩
      intro nonzero
      have nz : rd ≠ (0#5) := by
        intro zero; apply nonzero; simp [AddSub.Modular.Proofs.nativeInput, zero, zeroRegister]
      have index : entry.data.rs1 = rs1 := by
        rw [data]; simp [mopData, DecoderData.mapFamily, AddSub.Modular.nativeData, Trace.arithmeticFields, nz]
      rw [index] at reads
      exact (EStateM.Result.ok.inj (leftRead.symm.trans reads.1)).1
    · refine ⟨rightValue, rightRead, ?_⟩
      intro nonzero
      have nz : rd ≠ (0#5) := by
        intro zero; apply nonzero; simp [AddSub.Modular.Proofs.nativeInput, zero, zeroRegister]
      have index : entry.data.rs2 = rs2 := by
        rw [data]; simp [mopData, DecoderData.mapFamily, AddSub.Modular.nativeData, Trace.arithmeticFields, nz]
      rw [index] at reads
      exact (EStateM.Result.ok.inj (rightRead.symm.trans reads.2)).1
    · intro _ _
      have index : entry.data.rd = rd := by
        rw [data]
        exact AddSub.Modular.Proofs.native_rd opcode rs1 rs2 rd
      rw [index] at old
      simpa [AddSub.Modular.Proofs.nativeInput, lift, TriAdd.oldDestination,
        read_word, importedConstraintsMemoryPorts, WordColumns.evaluate] using old
    · exact pc

end Airbender.UnifiedReduced.Modular.Proofs
