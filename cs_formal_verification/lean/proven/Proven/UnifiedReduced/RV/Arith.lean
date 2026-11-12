module
public import Proven.UnifiedReduced.RV.Step

@[expose] public section

/-! ADD/SUB/ADDI/LUI/AUIPC and TRIADD rows (decoder bits 0–9) on the RV route. -/

namespace Airbender.UnifiedReduced.Proofs.RV
open Arithmetic Trace Trace.Proofs
set_option warningAsError true
set_option maxRecDepth 16384

/-- A row on the add/sub family bits (mask below `2^10`): its flags, operand registers, destination register update
    and PC successor. -/
theorem family_one {p : Nat} [Fact p.Prime] (hp : 4194304 ≤ p) {words : Nat → BitVec 32} {cells : List Cell}
    {epoch : Nat} {w : Nat → ZMod p} {s after : RV.State} {entry : RVProgramEntry} {i : RV.Instr}
    (facts : RowFacts words cells epoch w s after entry i) (small : entry.data.mask < 1024) :
    (∀ k : Fin 10, w (11 + k.val) = if entry.data.mask.testBit k.val then 1 else 0) ∧
    s.getReg entry.data.rs1 = (Word.mk (w 36).val (w 37).val).toBitVec ∧
    s.getReg entry.data.rs2 = (Word.mk (w 42).val (w 43).val).toBitVec ∧
    s.getReg entry.data.rd = (Word.mk (w 48).val (w 49).val).toBitVec ∧
    RV.Same after (s.setReg entry.data.rd (Word.mk (w 50).val (w 51).val).toBitVec) ∧
    (Word.mk (w 30).val (w 31).val).toBitVec = s.pc + 4 := by
  have flags := facts.flags (by omega)
  have high (k : Fin 19) (large : 10 ≤ k.val) : w (11 + k.val) = 0 := by
    have power : (1024 : Nat) ≤ 2 ^ k.val :=
      calc (1024 : Nat) = 2 ^ 10 := by norm_num
        _ ≤ 2 ^ k.val := Nat.pow_le_pow_right (by norm_num) large
    rw [flags k, Nat.testBit_eq_false_of_lt (lt_of_lt_of_le small power)]
    rfl
  have indices := facts.indices (by dsimp [limbBase]; omega)
  have reads := rv_register_reads (by dsimp [limbBase]; omega) facts.core (high 17 (by decide)) facts.query
    epoch facts.history
  have write := rv_register_write facts.core (high 18 (by decide)) indices.2.2 epoch facts.history
  have pc := facts.nextPC hp ⟨high 10 (by decide), high 11 (by decide), high 12 (by decide), high 13 (by decide)⟩
  exact ⟨fun k => flags ⟨k.val, by omega⟩, reads.1, reads.2, write.1, write.2, pc⟩

private theorem zero_word {p : Nat} [Fact p.Prime] {a b : ZMod p} {s : RV.State}
    (read : s.getReg 0 = (Word.mk a.val b.val).toBitVec) : (Word.mk a.val b.val).toBitVec = 0 := by
  rw [← read]; rfl

/-- ADD, SUB, ADDI, LUI and AUIPC rows. -/
theorem arith_step {p : Nat} [Fact p.Prime] (hp : 4194304 ≤ p) {words : Nat → BitVec 32} {cells : List Cell}
    {epoch : Nat} {w : Nat → ZMod p} {s after : RV.State} {entry : RVProgramEntry} {i : RV.Instr}
    (facts : RowFacts words cells epoch w s after entry i) (word : rvWordFields i = some entry.data)
    (small : entry.data.mask < 1024) : RowStep w s after i := by
  have hp' : 196608 < p := by omega
  obtain ⟨flags, left, right, _, write, pc⟩ := family_one hp facts small
  have immediate := facts.immediate (by dsimp [limbBase]; omega)
  have immediateBound : (Word.mk (w 8).val (w 9).val).Bounded := immediate ▸ (rv_field_bounds facts.fields).1
  have bit (k : Fin 10) (m : Nat) (mask : entry.data.mask = m) :
      w (11 + k.val) = if m.testBit k.val then 1 else 0 := mask ▸ flags k
  unfold rvWordFields at word
  split at word
  · -- ADD
    rename_i rd rs1 rs2
    have data := (Option.some.inj word).symm
    have mask : entry.data.mask = 1 := by rw [data]
    have value := add_limbs hp' facts.core (by simpa [Nat.testBit] using bit 0 1 mask)
      ⟨by simpa [Nat.testBit] using bit 1 1 mask, by simpa [Nat.testBit] using bit 2 1 mask,
        by simpa [Nat.testBit] using bit 3 1 mask, by simpa [Nat.testBit] using bit 4 1 mask,
        by simpa [Nat.testBit] using bit 5 1 mask, by simpa [Nat.testBit] using bit 6 1 mask,
        by simpa [Nat.testBit] using bit 9 1 mask⟩ facts.leftBound facts.rightBound immediateBound
    rw [data] at left right write immediate
    dsimp only at left right write immediate
    rw [immediate] at value
    refine ⟨_, RV.exec_op s .add rd rs1 rs2, ?_⟩
    have result : RV.alu .add (s.getReg rs1) (s.getReg rs2) = (Word.mk (w 50).val (w 51).val).toBitVec := by
      rw [value, left, right]
      simp [RV.alu, Word.toBitVec, Word.value]
    rw [result]
    exact rv_register_next write pc
  · -- SUB
    rename_i rd rs1 rs2
    have data := (Option.some.inj word).symm
    have mask : entry.data.mask = 2 := by rw [data]
    have value := sub_limbs hp' facts.core (by simpa [Nat.testBit] using bit 1 2 mask)
      ⟨by simpa [Nat.testBit] using bit 0 2 mask, by simpa [Nat.testBit] using bit 2 2 mask,
        by simpa [Nat.testBit] using bit 3 2 mask, by simpa [Nat.testBit] using bit 4 2 mask,
        by simpa [Nat.testBit] using bit 5 2 mask, by simpa [Nat.testBit] using bit 6 2 mask,
        by simpa [Nat.testBit] using bit 9 2 mask⟩ facts.leftBound facts.rightBound
    rw [data] at left right write
    dsimp only at left right write
    refine ⟨_, RV.exec_op s .sub rd rs1 rs2, ?_⟩
    have result : RV.alu .sub (s.getReg rs1) (s.getReg rs2) = (Word.mk (w 50).val (w 51).val).toBitVec := by
      rw [value, left, right]
      rfl
    rw [result]
    exact rv_register_next write pc
  · -- ADDI
    rename_i rd rs1 imm
    have data := (Option.some.inj word).symm
    have mask : entry.data.mask = 1 := by rw [data]
    have value := add_limbs hp' facts.core (by simpa [Nat.testBit] using bit 0 1 mask)
      ⟨by simpa [Nat.testBit] using bit 1 1 mask, by simpa [Nat.testBit] using bit 2 1 mask,
        by simpa [Nat.testBit] using bit 3 1 mask, by simpa [Nat.testBit] using bit 4 1 mask,
        by simpa [Nat.testBit] using bit 5 1 mask, by simpa [Nat.testBit] using bit 6 1 mask,
        by simpa [Nat.testBit] using bit 9 1 mask⟩ facts.leftBound facts.rightBound immediateBound
    rw [data] at left right write immediate
    dsimp only at left right write immediate
    rw [zero_word right, immediate, Word.ofBitVec_roundtrip] at value
    refine ⟨_, RV.exec_opImm s .add rd rs1 imm, ?_⟩
    have result : RV.alu .add (s.getReg rs1) imm = (Word.mk (w 50).val (w 51).val).toBitVec := by
      rw [value, left]
      simp [RV.alu]
    rw [result]
    exact rv_register_next write pc
  · -- LUI
    rename_i rd imm
    have data := (Option.some.inj word).symm
    have mask : entry.data.mask = 1 := by rw [data]
    have value := add_limbs hp' facts.core (by simpa [Nat.testBit] using bit 0 1 mask)
      ⟨by simpa [Nat.testBit] using bit 1 1 mask, by simpa [Nat.testBit] using bit 2 1 mask,
        by simpa [Nat.testBit] using bit 3 1 mask, by simpa [Nat.testBit] using bit 4 1 mask,
        by simpa [Nat.testBit] using bit 5 1 mask, by simpa [Nat.testBit] using bit 6 1 mask,
        by simpa [Nat.testBit] using bit 9 1 mask⟩ facts.leftBound facts.rightBound immediateBound
    rw [data] at left right write immediate
    dsimp only at left right write immediate
    rw [zero_word left, zero_word right, immediate, Word.ofBitVec_roundtrip] at value
    refine ⟨_, RV.exec_lui s rd imm, ?_⟩
    have result : imm = (Word.mk (w 50).val (w 51).val).toBitVec := by
      rw [value]
      simp
    rw [result]
    exact rv_register_next write pc
  · -- AUIPC
    rename_i rd imm
    have data := (Option.some.inj word).symm
    have mask : entry.data.mask = 4 := by rw [data]
    have pcWord := facts.pcWord (by dsimp [limbBase]; omega)
    have value := auipc_limbs hp' facts.core (by simpa [Nat.testBit] using bit 2 4 mask)
      ⟨by simpa [Nat.testBit] using bit 0 4 mask, by simpa [Nat.testBit] using bit 1 4 mask,
        by simpa [Nat.testBit] using bit 3 4 mask, by simpa [Nat.testBit] using bit 4 4 mask,
        by simpa [Nat.testBit] using bit 5 4 mask, by simpa [Nat.testBit] using bit 6 4 mask,
        by simpa [Nat.testBit] using bit 9 4 mask⟩ (pcWord ▸ Word.ofBitVec_bound _) immediateBound
    rw [data] at write immediate
    dsimp only at write immediate
    rw [pcWord, immediate, Word.ofBitVec_roundtrip, Word.ofBitVec_roundtrip] at value
    refine ⟨_, RV.exec_auipc s rd imm, ?_⟩
    rw [← value]
    exact rv_register_next write pc
  · -- LW
    have data := (Option.some.inj word).symm
    rw [data] at small
    simp at small
  · -- SW
    have data := (Option.some.inj word).symm
    rw [data] at small
    simp at small
  · cases word

/-- TRIADD rows: `rd := rs1 + rs2 + rd` (`RV.mopVal .triAdd`). -/
theorem triadd_step {p : Nat} [Fact p.Prime] (hp : 4194304 ≤ p) {words : Nat → BitVec 32} {cells : List Cell}
    {epoch : Nat} {w : Nat → ZMod p} {s after : RV.State} {entry : RVProgramEntry}
    {rd rs1 rs2 : RV.Reg}
    (facts : RowFacts words cells epoch w s after entry (.mop .triAdd rd rs1 rs2))
    (data : entry.data = ⟨.machine, rs1, rs2, rd, ⟨0, 0⟩, 512, 0⟩) :
    RowStep w s after (.mop .triAdd rd rs1 rs2) := by
  have mask : entry.data.mask = 512 := by rw [data]
  obtain ⟨flags, left, right, old, write, pc⟩ := family_one hp facts (by omega)
  have bit (k : Fin 10) : w (11 + k.val) = if (512 : Nat).testBit k.val then 1 else 0 := mask ▸ flags k
  have value := triadd_limbs (by omega) facts.core (by simpa [Nat.testBit] using bit 9)
    ⟨by simpa [Nat.testBit] using bit 0, by simpa [Nat.testBit] using bit 1,
      by simpa [Nat.testBit] using bit 2, by simpa [Nat.testBit] using bit 3,
      by simpa [Nat.testBit] using bit 4, by simpa [Nat.testBit] using bit 5,
      by simpa [Nat.testBit] using bit 6⟩ facts.leftBound facts.rightBound facts.oldBound
  rw [data] at left right old write
  dsimp only at left right old write
  refine ⟨_, RV.exec_mop s .triAdd rd rs1 rs2, ?_⟩
  have result : RV.mopVal .triAdd (s.getReg rs1) (s.getReg rs2) (s.getReg rd) =
      (Word.mk (w 50).val (w 51).val).toBitVec := by
    rw [value, left, right, old]
    rfl
  rw [result]
  exact rv_register_next write pc

end Airbender.UnifiedReduced.Proofs.RV
