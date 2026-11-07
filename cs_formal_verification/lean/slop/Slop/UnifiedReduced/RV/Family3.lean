import Slop.UnifiedReduced.RV.Step
import Slop.UnifiedReduced.RV.BinaryResult
import Slop.UnifiedReduced.RV.BinaryOperands
import Slop.UnifiedReduced.RV.Shift
import Slop.UnifiedReduced.RV.XorRotateArithmetic

/-! Shift/binary rows (decoder bits 15–16) on the RV route: XOR/OR/AND (register and immediate), SLL/SRL/SRA
    (register and immediate), REV8 and XORROT. -/

namespace Airbender.UnifiedReduced.Proofs.RV
open Arithmetic Trace Trace.Proofs
set_option warningAsError true
set_option maxRecDepth 16384

/-- A row on one of the shift/binary bits: selectors, operand and destination registers, PC successor. -/
theorem family_three {p : Nat} [Fact p.Prime] (hp : 4194304 ≤ p) {words : Nat → BitVec 32} {cells : List Cell}
    {epoch : Nat} {w : Nat → ZMod p} {s after : RV.State} {entry : RVProgramEntry} {i : RV.Instr}
    (facts : RowFacts words cells epoch w s after entry i) {m : Nat} (mask : entry.data.mask = m)
    (shape : m = 32768 ∨ m = 65536) :
    w 26 = (if m = 32768 then 1 else 0) ∧ w 27 = (if m = 32768 then 0 else 1) ∧
    (w 21 = 0 ∧ w 22 = 0 ∧ w 23 = 0 ∧ w 24 = 0) ∧ w 28 = 0 ∧
    s.getReg entry.data.rs1 = (Word.mk (w 36).val (w 37).val).toBitVec ∧
    s.getReg entry.data.rs2 = (Word.mk (w 42).val (w 43).val).toBitVec ∧
    s.getReg entry.data.rd = (Word.mk (w 48).val (w 49).val).toBitVec ∧
    RV.Same after (s.setReg entry.data.rd (Word.mk (w 50).val (w 51).val).toBitVec) ∧
    (Word.mk (w 30).val (w 31).val).toBitVec = s.pc + 4 := by
  have flags := facts.flags (by omega)
  rw [mask] at flags
  have bit (k : Fin 19) (b : Bool) (eq : m.testBit k.val = b) : w (11 + k.val) = if b then 1 else 0 := by
    rw [flags k, eq]
  have zeros : w 21 = 0 ∧ w 22 = 0 ∧ w 23 = 0 ∧ w 24 = 0 ∧ w 28 = 0 ∧ w 29 = 0 := by
    rcases shape with rfl | rfl
    all_goals exact ⟨by simpa using bit 10 false (by decide), by simpa using bit 11 false (by decide),
      by simpa using bit 12 false (by decide), by simpa using bit 13 false (by decide),
      by simpa using bit 17 false (by decide), by simpa using bit 18 false (by decide)⟩
  have selected : w 26 = (if m = 32768 then 1 else 0) ∧ w 27 = (if m = 32768 then 0 else 1) := by
    rcases shape with rfl | rfl
    · exact ⟨by simpa using bit 15 true (by decide), by simpa using bit 16 false (by decide)⟩
    · exact ⟨by simpa using bit 15 false (by decide), by simpa using bit 16 true (by decide)⟩
  have indices := facts.indices (by dsimp [limbBase]; omega)
  have reads := rv_register_reads (by dsimp [limbBase]; omega) facts.core zeros.2.2.2.2.1 facts.query
    epoch facts.history
  have write := rv_register_write facts.core zeros.2.2.2.2.2 indices.2.2 epoch facts.history
  have pc := facts.nextPC hp ⟨zeros.1, zeros.2.1, zeros.2.2.1, zeros.2.2.2.1⟩
  exact ⟨selected.1, selected.2, ⟨zeros.1, zeros.2.1, zeros.2.2.1, zeros.2.2.2.1⟩, zeros.2.2.2.2.1,
    reads.1, reads.2, write.1, write.2, pc⟩

theorem RowFacts.funct3 {p : Nat} [Fact p.Prime] {words : Nat → BitVec 32} {cells : List Cell}
    {epoch : Nat} {w : Nat → ZMod p} {s after : RV.State} {entry : RVProgramEntry} {i : RV.Instr}
    (facts : RowFacts words cells epoch w s after entry i) : w 10 = (entry.data.funct3 : ZMod p) := by
  have tag := congrArg (fun q : Vector (ZMod p) 9 => q[7]) facts.query
  exact tag

private theorem zero_limbs {p : Nat} [Fact p.Prime] {a b : ZMod p} (bound : (Word.mk a.val b.val).Bounded)
    (zero : (Word.mk a.val b.val).toBitVec = 0) : a = 0 ∧ b = 0 := by
  have limbs := Word.eq_zero_of_bounded bound zero
  constructor <;> apply ZMod.val_injective
  · simpa using congrArg Word.lo limbs
  · simpa using congrArg Word.hi limbs

/-! ### XOR/OR/AND -/

theorem binary_reg_step {p : Nat} [Fact p.Prime] (hp : 4194304 ≤ p) (byteInverse : 256 * (-7864320 : ZMod p) = 1)
    {words : Nat → BitVec 32} {cells : List Cell} {epoch : Nat} {w : Nat → ZMod p} {s after : RV.State}
    {entry : RVProgramEntry} {op : RV.Op} {rd rs1 rs2 : RV.Reg} {tag : Nat}
    (facts : RowFacts words cells epoch w s after entry (.op op rd rs1 rs2))
    (valid : tag = 4 ∨ tag = 6 ∨ tag = 7) (agree : ∀ a b, RV.alu op a b = Verification.byteOperation tag a b)
    (data : entry.data = ⟨.machine, rs1, rs2, rd, ⟨0, 0⟩, 65536, Setup.binaryTag tag⟩) :
    RowStep w s after (.op op rd rs1 rs2) := by
  obtain ⟨s26, s27, other, load, left, right, _, write, pc⟩ := family_three hp facts (by rw [data]) (Or.inr rfl)
  simp only [show (65536 : Nat) ≠ 32768 by decide, ite_false] at s26 s27
  have funct3 := facts.funct3
  have immediate := facts.immediate (by dsimp [limbBase]; omega)
  rw [data] at funct3 left right write immediate
  dsimp only at funct3 left right write immediate
  have zero : w 8 = 0 ∧ w 9 = 0 := by
    have lo := congrArg Word.lo immediate
    have hi := congrArg Word.hi immediate
    exact ⟨by simpa using lo, by simpa using hi⟩
  have core := facts.core
  have leftBytes := binary_left_bytes (by omega) byteInverse core ⟨s26, s27⟩ other tag valid funct3
  have rightBytes := binary_register_bytes (by omega) byteInverse core ⟨s26, s27⟩ other load zero tag valid funct3
  have value := binary_destination (by omega) core ⟨s26, s27⟩ other tag valid funct3 leftBytes rightBytes
  refine ⟨_, RV.exec_op s op rd rs1 rs2, ?_⟩
  rw [agree, left, right, ← value]
  exact rv_register_next write pc

theorem binary_imm_step {p : Nat} [Fact p.Prime] (hp : 4194304 ≤ p) (byteInverse : 256 * (-7864320 : ZMod p) = 1)
    {words : Nat → BitVec 32} {cells : List Cell} {epoch : Nat} {w : Nat → ZMod p} {s after : RV.State}
    {entry : RVProgramEntry} {op : RV.Op} {rd rs1 : RV.Reg} {x : BitVec 12} {tag : Nat}
    (facts : RowFacts words cells epoch w s after entry (.opImm op rd rs1 (x.signExtend 32)))
    (valid : tag = 4 ∨ tag = 6 ∨ tag = 7) (agree : ∀ a b, RV.alu op a b = Verification.byteOperation tag a b)
    (data : entry.data = ⟨.machine, rs1, 0, rd, ShiftBinop.binaryImmediate (x.signExtend 32), 65536,
      Setup.binaryTag tag⟩) :
    RowStep w s after (.opImm op rd rs1 (x.signExtend 32)) := by
  obtain ⟨s26, s27, other, load, left, right, _, write, pc⟩ := family_three hp facts (by rw [data]) (Or.inr rfl)
  simp only [show (65536 : Nat) ≠ 32768 by decide, ite_false] at s26 s27
  have funct3 := facts.funct3
  have immediate := facts.immediate (by dsimp [limbBase]; omega)
  rw [data] at funct3 left right write immediate
  dsimp only at funct3 left right write immediate
  have packed : w 8 = ((x.signExtend 32).extractLsb' 0 8).toNat ∧ w 9 = ((x.signExtend 32).extractLsb' 8 8).toNat := by
    have lo := congrArg Word.lo immediate
    have hi := congrArg Word.hi immediate
    simp only [ShiftBinop.binaryImmediate] at lo hi
    constructor
    · rw [← ZMod.natCast_zmod_val (w 8), lo]
      simp [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
    · rw [← ZMod.natCast_zmod_val (w 9), hi]
      simp [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  have zeroRead := zero_limbs facts.rightBound (by rw [← right]; rfl)
  have core := facts.core
  have leftBytes := binary_left_bytes (by omega) byteInverse core ⟨s26, s27⟩ other tag valid funct3
  have rightBytes := binary_immediate_bytes (by omega) byteInverse core ⟨s26, s27⟩ other load x packed zeroRead
    tag valid funct3
  have value := binary_destination (by omega) core ⟨s26, s27⟩ other tag valid funct3 leftBytes rightBytes
  refine ⟨_, RV.exec_opImm s op rd rs1 _, ?_⟩
  rw [agree, left, ← value]
  exact rv_register_next write pc

/-! ### SLL/SRL/SRA and REV8 -/

private theorem right_low_byte [Fact p.Prime] (hp : 65536 < p)
    (inverse : 256 * (-7864320 : ZMod p) = 1) {w : Nat → ZMod p}
    (small : (w 76).val < 256 ∧ (-7864320 * (w 42 - w 76)).val < 256) :
    (w 76).val = ((Word.mk (w 42).val (w 43).val).toBitVec.extractLsb' 0 8).toNat := by
  have packed := byte_pair_value hp (w 76) (-7864320 * (w 42 - w 76)) (w 42) small.1 small.2
    (by linear_combination (w 42 - w 76) * inverse)
  simp only [Word.toBitVec, Word.value, limbBase, BitVec.extractLsb',
    BitVec.toNat_ofNat, Nat.shiftRight_zero]
  norm_num only [Nat.reducePow]
  rw [packed]
  omega

/-- The shift row's destination is `shiftOperation` of rs1's word by the given amount. -/
private theorem shift_value {p : Nat} [Fact p.Prime] (hp : 4194304 ≤ p)
    (byteInverse : 256 * (-7864320 : ZMod p) = 1) {words : Nat → BitVec 32} {cells : List Cell} {epoch : Nat}
    {w : Nat → ZMod p} {s after : RV.State} {entry : RVProgramEntry} {i : RV.Instr}
    (facts : RowFacts words cells epoch w s after entry i) (s26 : w 26 = 1) (s27 : w 27 = 0)
    (other : w 21 = 0 ∧ w 22 = 0 ∧ w 23 = 0 ∧ w 24 = 0) (tag : Nat)
    (valid : tag = 1 ∨ tag = 2 ∨ tag = 3 ∨ tag = 5) (funct3 : w 10 = (tag : ZMod p)) {n : Nat}
    (amount : (w 57 + w 8).val = n) (reverse : tag = 5 → n = 0) :
    (Word.mk (w 50).val (w 51).val).toBitVec =
      Verification.shiftOperation tag (Word.mk (w 36).val (w 37).val).toBitVec n := by
  have code : (w 10).val = tag := by
    rw [funct3, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
  have leftBytes := shift_left_bytes (by omega) byteInverse facts.core ⟨s26, s27⟩ other
  have result := shift_destination (by omega) facts.core ⟨s26, s27⟩ other _ leftBytes (code ▸ valid)
    (fun rev => amount.trans (reverse (code ▸ rev)))
  rw [code, amount] at result
  exact result

theorem shift_step {p : Nat} [Fact p.Prime] (hp : 4194304 ≤ p) (byteInverse : 256 * (-7864320 : ZMod p) = 1)
    {words : Nat → BitVec 32} {cells : List Cell} {epoch : Nat} {w : Nat → ZMod p} {s after : RV.State}
    {entry : RVProgramEntry} {i : RV.Instr} {rd rs1 rs2 : RV.Reg} {imm : Word} {tag : Nat}
    (facts : RowFacts words cells epoch w s after entry i)
    (valid : tag = 1 ∨ tag = 2 ∨ tag = 3 ∨ tag = 5)
    (data : entry.data = ⟨.machine, rs1, rs2, rd, imm, 32768, tag⟩)
    (form : (rs2 = 0 ∧ imm.hi = 0 ∧ imm.lo < 32) ∨ (imm = ⟨0, 0⟩)) (reverse : tag = 5 → rs2 = 0 ∧ imm = ⟨0, 0⟩)
    (exec : ∀ n, (rs2 = 0 → n = imm.lo) → (rs2 ≠ 0 ∨ imm = ⟨0, 0⟩ → n = (s.getReg rs2 |>.extractLsb' 0 5).toNat) →
      ∃ next, RV.exec s i = some next ∧
        RV.Same next (s.setReg rd (Verification.shiftOperation tag (s.getReg rs1) n)).nextInstr) :
    RowStep w s after i := by
  obtain ⟨s26, s27, other, load, left, right, _, write, pc⟩ := family_three hp facts (by rw [data]) (Or.inl rfl)
  simp only [ite_true] at s26 s27
  have funct3 := facts.funct3
  have immediate := facts.immediate (by dsimp [limbBase]; omega)
  rw [data] at funct3 left right write immediate
  dsimp only at funct3 left right write immediate
  have lo : (w 8).val = imm.lo := congrArg Word.lo immediate
  have hi : (w 9).val = imm.hi := congrArg Word.hi immediate
  have truncated := shift_amount (by omega) facts.core ⟨s26, s27⟩ other load
  have lowByte := right_low_byte (by omega) byteInverse ⟨truncated.1, truncated.2.1⟩
  -- The amount is the low five bits of rs2 (register form) or the immediate (immediate form, rs2 = x0).
  have amountReg : (w 8).val = 0 → (w 57 + w 8).val = (s.getReg rs2 |>.extractLsb' 0 5).toNat := by
    intro zero
    have zero8 : w 8 = 0 := by simpa using zero
    rw [zero8, add_zero, truncated.2.2, lowByte, Verification.low_byte_shift_amount, right]
  have amountImm : rs2 = 0 → (w 57 + w 8).val = imm.lo := by
    intro zero
    subst zero
    have zeroRead := zero_limbs facts.rightBound (by rw [← right]; rfl)
    have packed := byte_pair_value (by omega) (w 76) (-7864320 * (w 42 - w 76)) (w 42) truncated.1 truncated.2.1
      (by linear_combination (w 42 - w 76) * byteInverse)
    rw [zeroRead.1, ZMod.val_zero] at packed
    have zero76 : (w 76).val = 0 := by omega
    have zero57 : w 57 = 0 := by
      apply ZMod.val_injective
      simpa [zero76] using truncated.2.2
    rw [zero57, zero_add, lo]
  obtain ⟨next, run, same⟩ := exec (w 57 + w 8).val amountImm (by
    intro h
    rcases h with nonzero | zero
    · rcases form with ⟨zero, _⟩ | zero
      · exact absurd zero nonzero
      · exact amountReg (by rw [lo, zero])
    · exact amountReg (by rw [lo, zero]))
  have value := shift_value hp byteInverse facts s26 s27 other tag valid funct3 rfl (by
    intro rev
    obtain ⟨zero, zeroImm⟩ := reverse rev
    rw [amountImm zero, zeroImm])
  refine ⟨next, run, same.trans ?_⟩
  rw [left, ← value]
  exact rv_register_next write pc

/-! ### XORROT -/

theorem xorrot_step {p : Nat} [Fact p.Prime] (hp : 4194304 ≤ p) (byteInverse : 256 * (-7864320 : ZMod p) = 1)
    {words : Nat → BitVec 32} {cells : List Cell} {epoch : Nat} {w : Nat → ZMod p} {s after : RV.State}
    {entry : RVProgramEntry} {n : BitVec 5} {rd rs1 : RV.Reg} {tag : Nat}
    (facts : RowFacts words cells epoch w s after entry (.xorRot n rd rs1))
    (found : customRotationTag n = some tag)
    (data : entry.data = ⟨.machine, rs1, rd, rd, ⟨0, 0⟩, 65536, tag⟩) :
    RowStep w s after (.xorRot n rd rs1) := by
  obtain ⟨s26, s27, other, load, left, right, _, write, pc⟩ := family_three hp facts (by rw [data]) (Or.inr rfl)
  simp only [show (65536 : Nat) ≠ 32768 by decide, ite_false] at s26 s27
  have funct3 := facts.funct3
  have immediate := facts.immediate (by dsimp [limbBase]; omega)
  rw [data] at funct3 left right write immediate
  dsimp only at funct3 left right write immediate
  have zero : w 8 = 0 ∧ w 9 = 0 := by
    have lo := congrArg Word.lo immediate
    have hi := congrArg Word.hi immediate
    exact ⟨by simpa using lo, by simpa using hi⟩
  obtain ⟨kind, tagEq, rotation⟩ : ∃ kind : Fin 4, tag = 47 + kind.val ∧ #[16, 12, 8, 7][kind.val]! = n.toNat := by
    unfold customRotationTag at found
    split_ifs at found with h16 h12 h8 h7
    · cases found; exact ⟨0, rfl, by rw [h16]; rfl⟩
    · cases found; exact ⟨1, rfl, by rw [h12]; rfl⟩
    · cases found; exact ⟨2, rfl, by rw [h8]; rfl⟩
    · cases found; exact ⟨3, rfl, by rw [h7]; rfl⟩
  subst tagEq
  have funct3' : w 10 = (47 + kind.val : Nat) := funct3
  have bytes := xorrot_operand_bytes (by omega) byteInverse facts.core ⟨s26, s27⟩ other kind funct3' load zero
  have value := xorrot_destination (by omega) facts.core ⟨s26, s27⟩ other kind funct3' _ _ bytes.1 bytes.2
  refine ⟨_, rfl, ?_⟩
  have result : (s.getReg rd ^^^ s.getReg rs1).rotateRight n.toNat = (Word.mk (w 50).val (w 51).val).toBitVec := by
    rw [value, left, right, rotation, BitVec.xor_comm]
  rw [result]
  exact rv_register_next write pc

end Airbender.UnifiedReduced.Proofs.RV
