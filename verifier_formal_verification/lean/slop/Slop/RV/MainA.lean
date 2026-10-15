import Slop.RV.Combine
import Slop.RV.Poly
import Slop.RV.Init
import Slop.RV.Coeffs
import Slop.RV.Coeffs4
import Slop.RV.Code.main

/-! The first part of `main` (the same code in both images up to call offsets, so one proof script `main_a_proof`):
`init`, read the inputs, `combine`, `poly_eval`. -/

namespace RV
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false

set_option hygiene false in
/-- The proof of `main_a` for an image: its `main` code `code`, `init` proven by `initThm` at `initA`, `combine` at
`combA`, `poly_eval` at `polyA`, the `.rodata` load image at ROM `siro`. -/
macro "main_a_proof" code:ident initThm:ident initA:term:max combA:term:max polyA:term:max siro:term:max : tactic => `(tactic| (
    rv_code_facts_range hmain $code 0 11
    rv_steps 11 with hpc, h2
    rv_name T hT
    have hTrom : ∀ b : Word, b.toNat < ROM_END → T.mem b = S.mem b := by
      intro b hb; rw [← hT]
      simp (disch := first | assumption | (simp only [writable, ROM_END, RAM_END] at *; bv_omega)) only [rv_state, write_rom]
    have hT2 : T.getReg 2#5 = 0x13fffa0#32 := by rw [← hT]; rv_regs; try (rw [h2]; rfl)
    refine run_cont ($initThm $initA (by decide) (by decide) T (codeAt_of_rom hinit (by decide) hTrom)
      (codeAt_of_rom hmc (by rw [memcpy_length]; decide) hTrom) (by rw [← hT]; rv_regs)
      (by rw [hT2]; decide) (by rw [hT2]; decide) (by rw [hT2]; decide) (by rw [← hT]; rv_regs; decide)) ?_
    intro S1 ⟨hpc1, hm1, hrom1, hreg1⟩
    have hS1rom : ∀ b : Word, b.toNat < ROM_END → S1.mem b = S.mem b := fun b hb => by rw [hrom1 b hb, hTrom b hb]
    have hpc1' : S1.pc = 0x64#32 := by rw [hpc1, ← hT]; rv_regs
    have h21 : S1.getReg 2#5 = 0x13fffa0#32 := by
      rw [hreg1 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hT2]
    -- the input words: neither in the copied `.rodata` nor in the frames
    have hin : ∀ a : Word, 0x1401000 ≤ a.toNat → a.toNat < 0x1401014 → S1.mem a = S.mem a := by
      intro a h1 h2'
      rw [hm1 a (by rw [hT2]; bv_omega), blockCopy_outside _ _ _ _ _ (by bv_omega), ← hT]
      simp (disch := first | assumption | bv_omega) only [rv_state, write_outside]
    have rd : ∀ a : Word, 0x1401000 ≤ a.toNat → a.toNat + 4 ≤ 0x1401014 → read S1.mem a 4 = read S.mem a 4 :=
      fun a h1 h2' => read_congr _ _ _ _ (fun j hj => hin _ (by bv_omega) (by bv_omega))
    have hx1 := (rd 0x1401000#32 (by decide) (by decide)).trans hx
    have hy01 := (rd 0x1401004#32 (by decide) (by decide)).trans hy0
    have hy11 := (rd 0x1401008#32 (by decide) (by decide)).trans hy1
    have hy21 := (rd 0x140100c#32 (by decide) (by decide)).trans hy2
    have hy31 := (rd 0x1401010#32 (by decide) (by decide)).trans hy3
    have hmain1 := codeAt_of_rom hmain (by decide) hS1rom
    rv_clear_facts
    rv_code_facts_range hmain1 $code 11 20
    rv_steps 9 with hpc1', h21, hx1, hy01, hy11, hy21, hy31
    have hcomb1 := codeAt_of_rom hcomb (by decide) hS1rom
    have hinc1 := codeAt_of_rom hinc (by decide) hS1rom
    have hdbl1 := codeAt_of_rom hdbl (by decide) hS1rom
    apply run_callAt (combine_impl $combA (by decide))
    · rv_regs
    · intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with h | h <;> subst h
      · exact codeAt_mem_eq (by simp only [rv_state]) hinc1
      · exact codeAt_mem_eq (by simp only [rv_state]) hdbl1
    · rv_call_ok_mem hcomb1 Code.combine with h21
    rv_returned S2 hpc2 hpost2 hcs2 hmem2 with h21
    have hS2rom : ∀ b : Word, b.toNat < ROM_END → S2.mem b = S.mem b := fun b hb => by
      rw [hmem2 b (by simp only [BitVec.toNat_ofNat, ROM_END] at *; bv_omega)]; exact hS1rom b hb
    -- the tables, copied to RAM by `init`
    have hcopy : ∀ a : Word, (a - 0x1400000#32).toNat < 912 → S2.mem a = blockCopy T.mem 0x1400000#32 $siro 912 a := by
      intro a ha
      rw [hmem2 a (by bv_omega)]; exact hm1 a (by rw [hT2]; bv_omega)
    have hcoefT : CodeAt T $siro Code.COEFFS := codeAt_of_rom hcoef (by rw [coeffs_length]; decide) hTrom
    have hcoef4T : CodeAt T ($siro + BitVec.ofNat 32 0x190) Code.COEFFS4 :=
      codeAt_of_rom hcoef4 (by rw [coeffs4_length]; decide) hTrom
    have hcoef2 : CodeAt S2 0x1400000#32 Code.COEFFS :=
      codeAt_blockCopy_dst hcoefT hcopy (by rw [coeffs_length]; decide) (by decide)
    have htab2 : CodeMem S2.mem (0x1400000#32 + BitVec.ofNat 32 0x190) Code.COEFFS4 :=
      codeMem_blockCopy_off hcoef4T hcopy (by rw [coeffs4_length] <;> decide) (by decide) (by decide)
    have h22 : S2.getReg 2#5 = 0x13fffa0#32 := (hcs2 _ (by rv_callee_saved)).trans (by rv_regs <;> exact h21)
    have h92 : S2.getReg 9#5 = x := by rw [hcs2 _ (by rv_callee_saved)]; rv_regs
    have hmain2 := codeAt_of_rom hmain (by decide) hS2rom
    rv_clear_facts
    rv_code_facts_range hmain2 $code 20 26
    rv_steps 6 with hpc2, hpost2, h22, h92
    have hpoly2 := codeAt_of_rom hpoly (by decide) hS2rom
    have hmul2 := codeAt_of_rom hmul (by decide) hS2rom
    have hadd2 := codeAt_of_rom hadd (by decide) hS2rom
    apply run_callAtPre (poly_eval_impl $polyA (by decide) Code.COEFFS coeffs_le)
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
      · first | exact hxP | (rw [h92]; exact hxP)
    rv_returned S3 hpc3 hpost3 hcs3 hmem3 with h22
    have hS3rom : ∀ b : Word, b.toNat < ROM_END → S3.mem b = S.mem b := fun b hb => by
      rw [hmem3 b (by simp only [BitVec.toNat_ofNat, ROM_END] at *; bv_omega)]
      first | exact hS2rom b hb | (simp only [rv_state]; exact hS2rom b hb)
    have hmain3 := codeAt_of_rom hmain (by decide) hS3rom
    rv_clear_facts
    rv_code_facts_range hmain3 $code 26 27
    simp only [polyPost] at hpost3
    rv_regs at hpost3
    rv_steps 1 with hpc3
    rv_ret
    refine ⟨by rv_regs; rw [hpc3]; decide, ?_, ?_, hpost3.1, hpost3.2, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals try rv_regs
    · rw [hcs3 _ (by rv_callee_saved)]; rv_regs <;> exact h22
    · rw [hcs3 _ (by rv_callee_saved)]; rv_regs
    · rw [hcs3 _ (by rv_callee_saved)]; rv_regs; rw [hcs2 _ (by rv_callee_saved)]; rv_regs
    · rw [hcs3 _ (by rv_callee_saved)]; rv_regs; rw [hcs2 _ (by rv_callee_saved)]; rv_regs
    · rw [hcs3 _ (by rv_callee_saved)]; rv_regs; rw [hcs2 _ (by rv_callee_saved)]; rv_regs
    · rw [hcs3 _ (by rv_callee_saved)]; rv_regs; rw [hcs2 _ (by rv_callee_saved)]; rv_regs
    · intro i hi
      simp only [rv_state]
      rw [read_congr _ S2.mem _ 4 (fun j hj => hmem3 _ (by rw [coeffs4_length] at hi; bv_omega))]
      exact htab2 i hi
    · intro b hb; simp only [rv_state]; exact hS3rom b hb
))

/-- From `main`'s entry: `init`, the inputs, `combine` and `poly_eval`; up to `main + 0x6c`. -/
theorem main_a (S : State) (x y0 y1 y2 y3 : Word) (hpc : S.pc = 0x38#32) (h2 : S.getReg 2#5 = 0x13ffff0#32)
    (hra : (S.getReg 1#5).toNat % 4 = 0)
    (hmain : CodeAt S 0x38#32 Code.main) (hinit : CodeAt S 0x9f8#32 Code.init)
    (hmc : CodeAt S 0xa80#32 Code.memcpy) (hcomb : CodeAt S 0x7c4#32 Code.combine)
    (hinc : CodeAt S 0x830#32 Code.inc) (hdbl : CodeAt S 0x80c#32 Code.double)
    (hpoly : CodeAt S 0x748#32 Code.poly_eval) (hmul : CodeAt S 0x70c#32 Code.mul_mod)
    (hadd : CodeAt S 0x6d8#32 Code.add_mod) (hcoef : CodeAt S 0x24b0#32 Code.COEFFS)
    (hcoef4 : CodeAt S (0x24b0#32 + BitVec.ofNat 32 0x190) Code.COEFFS4)
    (hx : read S.mem 0x1401000#32 4 = x) (hy0 : read S.mem 0x1401004#32 4 = y0)
    (hy1 : read S.mem 0x1401008#32 4 = y1) (hy2 : read S.mem 0x140100c#32 4 = y2)
    (hy3 : read S.mem 0x1401010#32 4 = y3) (hxP : x.toNat ≤ P) :
    ∃ m T, run m S = some T ∧ T.pc = 0xa4#32 ∧ T.getReg 2#5 = 0x13fffa0#32 ∧ T.getReg 18#5 = 3#32 * x + 1#32 ∧
      (T.getReg 9#5).toNat ≤ P ∧ (T.getReg 9#5).toNat % P = polyW Code.COEFFS x.toNat % P ∧
      T.getReg 19#5 = y3 ∧ T.getReg 20#5 = y2 ∧ T.getReg 21#5 = y1 ∧ T.getReg 22#5 = y0 ∧
      CodeMem T.mem (0x1400000#32 + BitVec.ofNat 32 0x190) Code.COEFFS4 ∧
      (∀ b : Word, b.toNat < ROM_END → T.mem b = S.mem b) := by
  main_a_proof Code.main init_run (0x9f8#32) (0x7c4#32) (0x748#32) (0x24b0#32)

end RV
