import Slop.RV.Combine
import Slop.RV.Poly
import Slop.RV.Init
import Slop.RV.Finish
import Slop.RV.FinishExt
import Slop.RV.Code.boot
import Slop.RV.Coeffs

/-! The whole program, booting like the real Airbender guests (riscv_common): `_start` → `_start_rust` → `main` →
`init` (copies `.rodata`, including the coefficient table, to RAM) → read `INPUT` → `combine` → `poly_eval` (on the
table in RAM) → `zksync_os_finish_success` → `…_extended` → its final self-jump. -/

namespace RV
set_option maxHeartbeats 0

/-- From reset (`pc = 0`, any registers), with the code and the `.rodata` image in ROM and a field element `x` at
`INPUT`, the program reaches the final self-jump of `zksync_os_finish_success_extended` (`0x3c0`) with
`a0 = 3x + 1`, `a1 ≡ polyW COEFFS x (mod P)`, `a1 ≤ P`, `x12 … x25 = 0` (riscv_common's output protocol), and the
halt word still in place. -/
theorem program_run (s : State) (x : Word) (hpc : s.pc = 0)
    (hboot : CodeAt s 0 Code.boot) (hinit : CodeAt s 0x3c4 Code.init) (hmc : CodeAt s 0x44c Code.memcpy)
    (hcomb : CodeAt s 0xd8 Code.combine) (hinc : CodeAt s 0x144 Code.inc) (hdbl : CodeAt s 0x120 Code.double)
    (hpoly : CodeAt s 0x1a4 Code.poly_eval) (hmul : CodeAt s 0x168 Code.mul_mod) (hadd : CodeAt s 0xa4 Code.add_mod)
    (hfin : CodeAt s 0x2c8 Code.finish_success) (hext : CodeAt s 0x340 Code.finish_success_extended)
    (hcoef : CodeAt s 0x1e7c Code.COEFFS) (hx : x.toNat ≤ P)
    (hin : read s.mem 0x1401000 4 = x) :
    ∃ n s', run n s = some s' ∧ s'.pc = 0x3c0#32 ∧ s'.getReg 10 = 3 * x + 1 ∧
      (s'.getReg 11).toNat ≤ P ∧ (s'.getReg 11).toNat % P = polyW Code.COEFFS x.toNat % P ∧
      (∀ i : Reg, 12 ≤ i.toNat → i.toNat ≤ 25 → s'.getReg i = 0) ∧ read s'.mem 0x3c0 4 = 0x0000006f := by
  simp only [BitVec.ofNat_eq_ofNat] at hpc hboot hinit hmc hin hcomb hinc hdbl hpoly hmul hadd hfin hext hcoef
  rv_code_facts hboot Code.boot
  rv_steps 21 with hpc
  rv_name T hT
  have hTrom : ∀ b : Word, b.toNat < ROM_END → T.mem b = s.mem b := by
    intro b hb; rw [← hT]
    simp (disch := first | assumption | (simp only [writable, ROM_END, RAM_END]; bv_omega)) only [rv_state, write_rom]
  have hT2 : T.getReg 2#5 = 20971456#32 := by rw [← hT]; rv_regs
  refine run_cont (init_run 0x3c4#32 (by decide) (by decide) T (codeAt_of_rom hinit (by decide) hTrom)
    (codeAt_of_rom hmc (by rw [memcpy_length]; decide) hTrom) (by rw [← hT]; rv_regs)
    (by rw [hT2]; decide) (by rw [hT2]; decide) (by rw [hT2]; decide) (by rw [← hT]; rv_regs; decide)) ?_
  intro S1 ⟨hpc1, hm1, hrom1, hreg1⟩
  have hS1rom : ∀ b : Word, b.toNat < ROM_END → S1.mem b = s.mem b := fun b hb => by rw [hrom1 b hb, hTrom b hb]
  have hpc1' : S1.pc = 84#32 := by rw [hpc1, ← hT]; rv_regs
  have h2' : S1.getReg 2#5 = 20971456#32 := by rw [hreg1 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hT2]
  have hx1 : read S1.mem 20975616#32 4 = x := by
    rw [← hin]
    apply read_congr; intro j hj
    rw [hm1 _ (by rw [hT2]; bv_omega), blockCopy_outside _ _ _ _ _ (by bv_omega), ← hT]
    simp (disch := first | assumption | (simp only [writable, ROM_END, RAM_END]; bv_omega)) only [rv_state]
    simp (disch := bv_omega) only [write_outside]
  have hboot1 := codeAt_of_rom hboot (by decide) hS1rom
  rv_clear_facts
  rv_code_facts hboot1 Code.boot
  have hcomb1 := codeAt_of_rom hcomb (by decide) hS1rom
  have hinc1 := codeAt_of_rom hinc (by decide) hS1rom
  have hdbl1 := codeAt_of_rom hdbl (by decide) hS1rom
  rv_steps 4 with hpc1', h2', hx1
  apply run_callAt (combine_impl 0xd8#32 (by decide))
  · rv_regs
  · intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with h | h <;> subst h
    · exact codeAt_mem_eq (by simp only [rv_state]) hinc1
    · exact codeAt_mem_eq (by simp only [rv_state]) hdbl1
  · rv_call_ok_mem hcomb1 Code.combine with h2'
  rv_returned S2 hpc2 hpost2 hcs2 hmem2 with h2'
  have hcoefT : CodeAt T 7804#32 Code.COEFFS := codeAt_of_rom hcoef (by rw [coeffs_length]; decide) hTrom
  have hcoef2 : CodeAt S2 20971520#32 Code.COEFFS := by
    refine codeAt_blockCopy_dst (n := 400) hcoefT (fun a ha => ?_) (by rw [coeffs_length]; decide) (by decide)
    rw [hmem2 a (by simp only [BitVec.toNat_ofNat]; bv_omega), hm1 a (by rw [hT2]; bv_omega)]
  have hS2rom : ∀ b : Word, b.toNat < ROM_END → S2.mem b = s.mem b := fun b hb => by
    rw [hmem2 b (by simp only [BitVec.toNat_ofNat, ROM_END] at *; bv_omega), hS1rom b hb]
  have h22 : S2.getReg 2#5 = 20971456#32 := by rw [hcs2 _ (by rv_callee_saved)]; rv_regs; exact h2'
  have h92 : S2.getReg 9#5 = x := by rw [hcs2 _ (by rv_callee_saved)]; rv_regs
  have hpoly2 := codeAt_of_rom hpoly (by decide) hS2rom
  have hmul2 := codeAt_of_rom hmul (by decide) hS2rom
  have hadd2 := codeAt_of_rom hadd (by decide) hS2rom
  have hboot2 := codeAt_of_rom hboot (by decide) hS2rom
  rv_clear_facts
  rv_code_facts hboot2 Code.boot
  rv_steps 6 with hpc2, hpost2, h22, h92
  apply run_callAtPre (poly_eval_impl 0x1a4#32 (by decide) Code.COEFFS coeffs_le)
  · rv_regs
  · intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with h | h <;> subst h
    · exact codeAt_mem_eq (by simp only [rv_state]) hmul2
    · exact codeAt_mem_eq (by simp only [rv_state]) hadd2
  · rv_call_ok_mem hpoly2 Code.poly_eval with h22
  · simp only [polyPre]
    rv_regs
    refine ⟨codeAt_mem_eq (by simp only [rv_state]) hcoef2, by rw [coeffs_length], ?_, ?_, by decide, ?_⟩
    · rw [coeffs_length, h22]; right; decide
    · rw [coeffs_length]; decide
    · first | exact hx | (rw [h92]; exact hx)
  rv_returned S3 hpc3 hpost3 hcs3 hmem3 with h22
  have hS3rom : ∀ b : Word, b.toNat < ROM_END → S3.mem b = s.mem b := fun b hb => by
    rw [hmem3 b (by simp only [BitVec.toNat_ofNat, ROM_END] at *; bv_omega)]
    first | exact hS2rom b hb | (simp only [rv_state]; exact hS2rom b hb)
  have h23 : S3.getReg 2#5 = 20971456#32 := by rw [hcs3 _ (by rv_callee_saved)]; rv_regs; try exact h22
  have h183 : S3.getReg 18#5 = 3#32 * x + 1#32 := by rw [hcs3 _ (by rv_callee_saved)]; rv_regs; try exact hpost2
  have hboot3 := codeAt_of_rom hboot (by decide) hS3rom
  rv_clear_facts
  rv_code_facts hboot3 Code.boot
  rv_steps 10 with hpc3, h23, h183
  rv_name T3 hT3
  have hT3rom : ∀ b : Word, b.toNat < ROM_END → T3.mem b = s.mem b := by
    intro b hb; rw [← hT3, ← hS3rom b hb]
    simp (disch := first | assumption | (simp only [writable, ROM_END, RAM_END]; bv_omega)) only [rv_state, write_rom]
  have hT32 : T3.getReg 2#5 = 20971456#32 := by rw [← hT3]; rv_regs; exact h23
  refine run_cont (finish_success_run T3 (codeAt_of_rom hfin (by decide) hT3rom) (by rw [← hT3]; rv_regs)
    (by rw [← hT3]; rv_regs; rw [h23]) (3#32 * x + 1#32) (S3.getReg 10#5) 0 0 0 0 0 0
    (by rw [hT32, ← hT3]; simp (disch := first | decide | rv_disch) only [rv_state, read_write_same4, read_write_disjoint])
    (by rw [hT32, ← hT3]; simp (disch := first | decide | rv_disch) only [rv_state, read_write_same4, read_write_disjoint, BitVec.reduceAdd])
    (by rw [hT32, ← hT3]; simp (disch := first | decide | rv_disch) only [rv_state, read_write_same4, read_write_disjoint, BitVec.reduceAdd])
    (by rw [hT32, ← hT3]; simp (disch := first | decide | rv_disch) only [rv_state, read_write_same4, read_write_disjoint, BitVec.reduceAdd])
    (by rw [hT32, ← hT3]; simp (disch := first | decide | rv_disch) only [rv_state, read_write_same4, read_write_disjoint, BitVec.reduceAdd])
    (by rw [hT32, ← hT3]; simp (disch := first | decide | rv_disch) only [rv_state, read_write_same4, read_write_disjoint, BitVec.reduceAdd])
    (by rw [hT32, ← hT3]; simp (disch := first | decide | rv_disch) only [rv_state, read_write_same4, read_write_disjoint, BitVec.reduceAdd])
    (by rw [hT32, ← hT3]; simp (disch := first | decide | rv_disch) only [rv_state, read_write_same4, read_write_disjoint, BitVec.reduceAdd])
    (by rw [hT32]; decide) (by rw [hT32]; decide) (by rw [hT32]; decide)) ?_
  intro S4 ⟨hpc4, h24, h104, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, hrom4⟩
  have hS4rom : ∀ b : Word, b.toNat < ROM_END → S4.mem b = s.mem b := fun b hb => by rw [hrom4 b hb, hT3rom b hb]
  refine run_cont (finish_extended_run S4 (codeAt_of_rom hext (by decide) hS4rom) hpc4
    (by rw [h104, h24, hT32]; decide) (3#32 * x + 1#32) (S3.getReg 10#5) 0 0 0 0 0 0 0 0 0 0 0 0 0 0
    (by rw [h24, hT32]; rw [hT32] at f0; simpa only [BitVec.add_assoc, BitVec.reduceAdd] using f0) (by rw [h24, hT32]; rw [hT32] at f1; simpa only [BitVec.add_assoc, BitVec.reduceAdd] using f1)
    (by rw [h24, hT32]; rw [hT32] at f2; simpa only [BitVec.add_assoc, BitVec.reduceAdd] using f2) (by rw [h24, hT32]; rw [hT32] at f3; simpa only [BitVec.add_assoc, BitVec.reduceAdd] using f3)
    (by rw [h24, hT32]; rw [hT32] at f4; simpa only [BitVec.add_assoc, BitVec.reduceAdd] using f4) (by rw [h24, hT32]; rw [hT32] at f5; simpa only [BitVec.add_assoc, BitVec.reduceAdd] using f5)
    (by rw [h24, hT32]; rw [hT32] at f6; simpa only [BitVec.add_assoc, BitVec.reduceAdd] using f6) (by rw [h24, hT32]; rw [hT32] at f7; simpa only [BitVec.add_assoc, BitVec.reduceAdd] using f7)
    (by rw [h24, hT32]; rw [hT32] at f8; simpa only [BitVec.add_assoc, BitVec.reduceAdd] using f8) (by rw [h24, hT32]; rw [hT32] at f9; simpa only [BitVec.add_assoc, BitVec.reduceAdd] using f9)
    (by rw [h24, hT32]; rw [hT32] at f10; simpa only [BitVec.add_assoc, BitVec.reduceAdd] using f10) (by rw [h24, hT32]; rw [hT32] at f11; simpa only [BitVec.add_assoc, BitVec.reduceAdd] using f11)
    (by rw [h24, hT32]; rw [hT32] at f12; simpa only [BitVec.add_assoc, BitVec.reduceAdd] using f12) (by rw [h24, hT32]; rw [hT32] at f13; simpa only [BitVec.add_assoc, BitVec.reduceAdd] using f13)
    (by rw [h24, hT32]; rw [hT32] at f14; simpa only [BitVec.add_assoc, BitVec.reduceAdd] using f14) (by rw [h24, hT32]; rw [hT32] at f15; simpa only [BitVec.add_assoc, BitVec.reduceAdd] using f15)
    (by rw [h24, hT32]; decide) (by rw [h24, hT32]; decide) (by rw [h24, hT32]; decide)) ?_
  intro S5 ⟨hpc5, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, hrom5⟩
  have hpoly3 := hpost3
  simp only [polyPost] at hpoly3
  rv_regs at hpoly3
  refine ⟨0, S5, rfl, hpc5, by rw [r10], by rw [r11]; exact hpoly3.1, by rw [r11]; exact hpoly3.2, ?_, ?_⟩
  · intro i h1 h2
    have : i = 12#5 ∨ i = 13#5 ∨ i = 14#5 ∨ i = 15#5 ∨ i = 16#5 ∨ i = 17#5 ∨ i = 18#5 ∨ i = 19#5 ∨ i = 20#5 ∨
      i = 21#5 ∨ i = 22#5 ∨ i = 23#5 ∨ i = 24#5 ∨ i = 25#5 := by bv_omega
    rcases this with h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst h <;> assumption
  · rw [read_congr _ s.mem _ 4 (fun j hj => by rw [hrom5 _ (by simp only [ROM_END]; bv_omega),
      hS4rom _ (by simp only [ROM_END]; bv_omega)])]
    have := hext 32 (by decide)
    simpa [Code.finish_success_extended] using this
end RV
