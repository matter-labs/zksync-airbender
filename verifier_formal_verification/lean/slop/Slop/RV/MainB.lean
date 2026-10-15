import Slop.RV.Coeffs4
import Slop.RV.Finish
import Slop.RV.FinishExt
import Slop.RV.Code.main

/-! The second part of `main` (both images, one proof script `main_b_proof`): `ext4_poly`, then the outputs. -/

namespace RV
open Spec
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false

set_option hygiene false in
/-- The proof of `main_b` for an image: its `main` code `code`, `zksync_os_finish_success` at `finA` and `…_extended`
at `extA`. -/
macro "main_b_proof" code:ident finA:term:max extA:term:max : tactic => `(tactic| (
    rv_code_facts_range hmain $code 27 34
    rv_steps 7 with hpc, h2, h19, h20, h21, h22
    rv_name U hU
    have hUm : ∀ a : Word, a.toNat < 0x13fffb0 ∨ 0x13fffc0 ≤ a.toNat → U.mem a = T.mem a := by
      intro a ha; rw [← hU]
      simp (disch := first | assumption | bv_omega) only [rv_state, write_outside]
    have hUrom : ∀ b : Word, b.toNat < ROM_END → U.mem b = T.mem b := fun b hb => hUm b (by simp only [ROM_END] at hb; omega)
    have u2 : U.getReg 2#5 = 0x13fffa0#32 := by rw [← hU]; rv_regs <;> exact h2
    have u10 : U.getReg 10#5 = 0x13fffa0#32 := by rw [← hU]; rv_regs
    have u11 : U.getReg 11#5 = 0x13fffb0#32 := by rw [← hU]; rv_regs
    apply run_callAtW hEP
    · rw [← hU]; rv_regs
    · intro c hc; exact codeAt_of_rom (hcal c hc) (hcalr c hc) hUrom
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [← hU] <;> rv_regs
      · rw [hU]; exact codeAt_of_rom hEPc (by simp only [ROM_END]; bv_omega) hUrom
      all_goals try simp only [ROM_END, RAM_END, h2]
      all_goals bv_omega
    · simp only [e4polyPre, argOk, RAM_END, u2, u10, u11]
      refine ⟨by decide, by decide, ?_, fun i hi => ?_, by decide⟩
      · rw [← hU]; simp only [canon4]
        simp (disch := rv_disch) only [rv_state, BitVec.reduceAdd, read_write_same4, read_write_disjoint]
        exact ⟨hy0, hy1, hy2, hy3⟩
      · rw [read_congr _ T.mem _ 4 (fun j hj => hUm _ (by rw [coeffs4_length] at hi; right; bv_omega))]; exact htab i hi
    rv_returned S1 hpc1 hpost1 hcs1 hmem1
    simp only [e4polyPost, u10, u11] at hpost1
    obtain ⟨hcO, hO⟩ := hpost1
    have hyU : limbsAt U.mem 0x13fffb0#32 = ofLimbs (y0.toNat : Spec.F) (y1.toNat : Spec.F) (y2.toNat : Spec.F) (y3.toNat : Spec.F) := by
      rw [← hU]; simp only [limbsAt]
      simp (disch := rv_disch) only [rv_state, BitVec.reduceAdd, read_write_same4, read_write_disjoint]
    rw [hyU] at hO
    have hS1rom : ∀ b : Word, b.toNat < ROM_END → S1.mem b = T.mem b := fun b hb => by
      rw [hmem1 b (by rw [u2]; simp only [ROM_END] at hb; bv_omega) (by rw [u10]; simp only [ROM_END] at hb; bv_omega),
        hUrom b hb]
    have hmain1 := codeAt_of_rom hmain (by decide) hS1rom
    have p1 : S1.pc = 0xc0#32 := by rw [hpc1, ← hU]; rv_regs
    have s2 : S1.getReg 2#5 = 0x13fffa0#32 := by rw [hcs1 _ (by rv_callee_saved), u2]
    have s18 : S1.getReg 18#5 = c := by rw [hcs1 _ (by rv_callee_saved), ← hU]; rv_regs <;> exact h18
    have s9 : S1.getReg 9#5 = p := by rw [hcs1 _ (by rv_callee_saved), ← hU]; rv_regs <;> exact h9
    rv_clear_facts
    rv_code_facts_range hmain1 $code 34 48
    rv_steps 14 with p1, s2, s18, s9
    rv_name V hV
    have hVrom : ∀ b : Word, b.toNat < ROM_END → V.mem b = T.mem b := by
      intro b hb; rw [← hV, ← hS1rom b hb]
      simp (disch := first | assumption | (simp only [writable, ROM_END, RAM_END]; bv_omega)) only [rv_state, write_rom]
    have hV2 : V.getReg 2#5 = 0x13fffa0#32 := by rw [← hV]; rv_regs <;> exact s2
    refine run_cont (finish_success_run $finA (by decide) (by decide) V (codeAt_of_rom hfin (by decide) hVrom)
      (by rw [← hV]; rv_regs) 0x13fffb0#32 (by rw [← hV]; rv_regs) c p
      (read S1.mem 0x13fffa0#32 4) (read S1.mem 0x13fffa4#32 4) (read S1.mem 0x13fffa8#32 4) (read S1.mem 0x13fffac#32 4)
      0 0
      (by rw [← hV]; simp (disch := first | decide | rv_disch) only [rv_state, BitVec.reduceAdd, read_write_same4, read_write_off, read_write_off0r, read_write_off0l, read_write_disjoint]) (by rw [← hV]; simp (disch := first | decide | rv_disch) only [rv_state, BitVec.reduceAdd, read_write_same4, read_write_off, read_write_off0r, read_write_off0l, read_write_disjoint]) (by rw [← hV]; simp (disch := first | decide | rv_disch) only [rv_state, BitVec.reduceAdd, read_write_same4, read_write_off, read_write_off0r, read_write_off0l, read_write_disjoint]) (by rw [← hV]; simp (disch := first | decide | rv_disch) only [rv_state, BitVec.reduceAdd, read_write_same4, read_write_off, read_write_off0r, read_write_off0l, read_write_disjoint]) (by rw [← hV]; simp (disch := first | decide | rv_disch) only [rv_state, BitVec.reduceAdd, read_write_same4, read_write_off, read_write_off0r, read_write_off0l, read_write_disjoint]) (by rw [← hV]; simp (disch := first | decide | rv_disch) only [rv_state, BitVec.reduceAdd, read_write_same4, read_write_off, read_write_off0r, read_write_off0l, read_write_disjoint]) (by rw [← hV]; simp (disch := first | decide | rv_disch) only [rv_state, BitVec.reduceAdd, read_write_same4, read_write_off, read_write_off0r, read_write_off0l, read_write_disjoint]) (by rw [← hV]; simp (disch := first | decide | rv_disch) only [rv_state, BitVec.reduceAdd, read_write_same4, read_write_off, read_write_off0r, read_write_off0l, read_write_disjoint]) 
      (by rw [hV2]; decide) (by rw [hV2]; decide) (by rw [hV2]; decide) (by decide) (by decide)) ?_
    intro S4 ⟨hpc4, h24, h104, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, hrom4⟩
    have hS4rom : ∀ b : Word, b.toNat < ROM_END → S4.mem b = T.mem b := fun b hb => by rw [hrom4 b hb, hVrom b hb]
    refine run_cont (finish_extended_run $extA (by decide) (by decide) S4 (codeAt_of_rom hext (by decide) hS4rom)
      (by rw [hpc4]; rfl) (by rw [h104, h24, hV2]; decide) c p (read S1.mem 0x13fffa0#32 4) (read S1.mem 0x13fffa4#32 4)
      (read S1.mem 0x13fffa8#32 4) (read S1.mem 0x13fffac#32 4) 0 0 0 0 0 0 0 0 0 0
      (by rw [h24, hV2]; rw [hV2] at f0; simpa only [BitVec.add_assoc, BitVec.reduceAdd] using f0) (by rw [h24, hV2]; rw [hV2] at f1; simpa only [BitVec.add_assoc, BitVec.reduceAdd] using f1) (by rw [h24, hV2]; rw [hV2] at f2; simpa only [BitVec.add_assoc, BitVec.reduceAdd] using f2) (by rw [h24, hV2]; rw [hV2] at f3; simpa only [BitVec.add_assoc, BitVec.reduceAdd] using f3) (by rw [h24, hV2]; rw [hV2] at f4; simpa only [BitVec.add_assoc, BitVec.reduceAdd] using f4) (by rw [h24, hV2]; rw [hV2] at f5; simpa only [BitVec.add_assoc, BitVec.reduceAdd] using f5) (by rw [h24, hV2]; rw [hV2] at f6; simpa only [BitVec.add_assoc, BitVec.reduceAdd] using f6) (by rw [h24, hV2]; rw [hV2] at f7; simpa only [BitVec.add_assoc, BitVec.reduceAdd] using f7) (by rw [h24, hV2]; rw [hV2] at f8; simpa only [BitVec.add_assoc, BitVec.reduceAdd] using f8) (by rw [h24, hV2]; rw [hV2] at f9; simpa only [BitVec.add_assoc, BitVec.reduceAdd] using f9) (by rw [h24, hV2]; rw [hV2] at f10; simpa only [BitVec.add_assoc, BitVec.reduceAdd] using f10) (by rw [h24, hV2]; rw [hV2] at f11; simpa only [BitVec.add_assoc, BitVec.reduceAdd] using f11) (by rw [h24, hV2]; rw [hV2] at f12; simpa only [BitVec.add_assoc, BitVec.reduceAdd] using f12) (by rw [h24, hV2]; rw [hV2] at f13; simpa only [BitVec.add_assoc, BitVec.reduceAdd] using f13) (by rw [h24, hV2]; rw [hV2] at f14; simpa only [BitVec.add_assoc, BitVec.reduceAdd] using f14) (by rw [h24, hV2]; rw [hV2] at f15; simpa only [BitVec.add_assoc, BitVec.reduceAdd] using f15)
      (by rw [h24, hV2]; decide) (by rw [h24, hV2]; decide) (by rw [h24, hV2]; decide)) ?_
    intro S5 ⟨hpc5, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, hrom5⟩
    -- the Ext4 limbs
    simp only [canon4] at hcO
    simp only [limbsAt] at hO
    refine ⟨0, S5, rfl, by rw [hpc5]; rfl, r10, r11, ?_, ?_, ?_, fun b hb => (hrom5 b hb).trans (hS4rom b hb)⟩
    · intro i h1 h2'
      rcases (by bv_omega : i = 12#5 ∨ i = 13#5 ∨ i = 14#5 ∨ i = 15#5) with h|h|h|h <;> subst h
      · rw [r12]; exact hcO.1
      · rw [r13]; simpa only [BitVec.add_assoc, BitVec.reduceAdd] using hcO.2.1
      · rw [r14]; simpa only [BitVec.add_assoc, BitVec.reduceAdd] using hcO.2.2.1
      · rw [r15]; simpa only [BitVec.add_assoc, BitVec.reduceAdd] using hcO.2.2.2
    · rw [r12, r13, r14, r15]; simpa only [BitVec.add_assoc, BitVec.reduceAdd] using hO
    · intro i h1 h2'
      have : i = 16#5 ∨ i = 17#5 ∨ i = 18#5 ∨ i = 19#5 ∨ i = 20#5 ∨ i = 21#5 ∨ i = 22#5 ∨ i = 23#5 ∨ i = 24#5 ∨
        i = 25#5 := by bv_omega
      rcases this with h|h|h|h|h|h|h|h|h|h <;> subst h <;> assumption
))

/-- From `main + 0x6c` (after `poly_eval`): the inputs `y` to the stack, `ext4_poly` (any implementation of its
contract), the 8 output words to `zksync_os_finish_success`, which ends at its final self-jump with the outputs in
`x10 … x25`. -/
theorem main_b (T : State) (c p y0 y1 y2 y3 : Word) (codeEP : List Word)
    (calleesEP : List (Word × List Word)) (FEP : Nat)
    (hEP : ImplementsAtW 0x5a4#32 codeEP calleesEP FEP e4polyPre 16 e4polyPost)
    (hEPr : 0x5a4 + 4 * codeEP.length ≤ 4194304) (hFEP : FEP ≤ 0x100000)
    (hcalr : ∀ c ∈ calleesEP, c.1.toNat + 4 * c.2.length ≤ 4194304)
    (hpc : T.pc = 0xa4#32) (h2 : T.getReg 2#5 = 0x13fffa0#32) (h18 : T.getReg 18#5 = c) (h9 : T.getReg 9#5 = p)
    (h19 : T.getReg 19#5 = y3) (h20 : T.getReg 20#5 = y2) (h21 : T.getReg 21#5 = y1) (h22 : T.getReg 22#5 = y0)
    (htab : CodeMem T.mem (0x1400000#32 + BitVec.ofNat 32 0x190) Code.COEFFS4)
    (hmain : CodeAt T 0x38#32 Code.main) (hEPc : CodeAt T 0x5a4#32 codeEP) (hcal : ∀ c ∈ calleesEP, CodeAt T c.1 c.2)
    (hfin : CodeAt T 0x8fc#32 Code.finish_success) (hext : CodeAt T 0x974#32 Code.finish_success_extended)
    (hy0 : y0.toNat < BabyBearP) (hy1 : y1.toNat < BabyBearP) (hy2 : y2.toNat < BabyBearP)
    (hy3 : y3.toNat < BabyBearP) :
    ∃ m W, run m T = some W ∧ W.pc = 0x9f4#32 ∧ W.getReg 10#5 = c ∧ W.getReg 11#5 = p ∧
      (∀ i : Reg, 12 ≤ i.toNat → i.toNat ≤ 15 → (W.getReg i).toNat < BabyBearP) ∧
      ofLimbs ((W.getReg 12#5).toNat : F) ((W.getReg 13#5).toNat : F) ((W.getReg 14#5).toNat : F)
        ((W.getReg 15#5).toNat : F) = poly4 (ofLimbs (y0.toNat : F) (y1.toNat : F) (y2.toNat : F) (y3.toNat : F)) ∧
      (∀ i : Reg, 16 ≤ i.toNat → i.toNat ≤ 25 → W.getReg i = 0) ∧
      (∀ b : Word, b.toNat < ROM_END → W.mem b = T.mem b) := by
  main_b_proof Code.main (0x8fc#32) (0x974#32)

end RV
