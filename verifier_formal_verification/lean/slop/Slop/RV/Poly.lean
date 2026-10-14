import Slop.RV.PolyEmpty

/-! `poly_eval` for `n ≥ 1`: prologue to the loop head, then the loop lemma; and the combined contract. -/

namespace RV

set_option maxHeartbeats 1000000 in
theorem poly_eval_nonempty (A : Word) (hA : 256 ≤ A.toNat) (C : List Word) (hn : 0 < C.length)
    (hC : ∀ i (h : i < C.length), C[i].toNat ≤ P) :
    ImplementsAtPre A Code.poly_eval [(A + 4294967236#32, Code.mul_mod), (A + 4294967040#32, Code.add_mod)] 48
      (polyPre C) (polyPost C) := by
  intro s hentry hcallees hcall hpre
  have hmul : CodeAt s (A + 4294967236#32) Code.mul_mod := hcallees (A + 4294967236#32, Code.mul_mod) (by simp)
  have hadd : CodeAt s (A + 4294967040#32) Code.add_mod := hcallees (A + 4294967040#32, Code.add_mod) (by simp)
  clear hcallees
  obtain ⟨hcoef, ha1, hT, hT4, hx⟩ := hpre
  simp only [BitVec.ofNat_eq_ofNat] at hcoef ha1 hT hT4 hx
  have hcode : CodeAt s A Code.poly_eval := hentry ▸ hcall.1
  rw [Call, hentry] at hcall
  rv_start Code.poly_eval hcall
  have hA4 : A.toNat % 4 = 0 := hpc
  rv_steps 15 with hentry, ha1
  refine exists_run_mono (poly_loop A (s.getReg 10#5) C hA (by omega) hT hT4 hC C.length _ (s.getReg 2#5) (s.getReg 1#5)
    (s.getReg 8#5) (s.getReg 9#5) (s.getReg 18#5) (s.getReg 19#5) (s.getReg 12#5) _ hn (Nat.le_refl _) ?_ ?_ ?_ ?_ ?_ rfl ?_ ?_ hx
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hsp (by omega) hhi hra hA4) ?_
  · rv_regs; rw [hentry]
  · rv_regs
  · rv_regs
  · rv_regs
  · rv_regs
    rw [ofNat_shl2 _ (by omega)]
    bv_omega
  · rv_regs; simp
  · rv_regs; simp [List.drop_length, polyW]
  all_goals first
    | (rv_step_simp with ha1; done)
    | skip
  · rv_codeAt hcode Code.poly_eval
  · rv_codeAt hmul Code.mul_mod
  · rv_codeAt hadd Code.add_mod
  · rv_codeAt hcoef C
  · intro s' ⟨hp, hr10a, hr10b, hr2, hr8, hr9, hr18, hr19, hcsL, hmemL⟩
    refine ⟨hp, ⟨hr10a, hr10b⟩, ?_, ?_⟩
    · intro i hi
      rcases calleeSaved_cases i hi with h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h
      all_goals first
        | assumption
        | (rw [hcsL _ (by decide) (by decide)]; rv_regs)
    · intro a ha
      rw [hmemL a ha]
      simp (disch := rv_disch) only [set_mem, next_mem, store_mem, jump_mem, write_outside]


theorem poly_eval_impl (A : Word) (hA : 256 ≤ A.toNat) (C : List Word)
    (hC : ∀ i (h : i < C.length), C[i].toNat ≤ P) :
    ImplementsAtPre A Code.poly_eval [(A + 4294967236#32, Code.mul_mod), (A + 4294967040#32, Code.add_mod)] 48
      (polyPre C) (polyPost C) := by
  rcases Nat.eq_zero_or_pos C.length with hn | hn
  · exact poly_eval_empty A hA C hn hC
  · exact poly_eval_nonempty A hA C hn hC

end RV
