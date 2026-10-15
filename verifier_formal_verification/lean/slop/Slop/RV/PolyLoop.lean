import Slop.RV.MulMod
import Slop.RV.Code.poly_eval

/-! The Horner loop of `poly_eval` (loop head at `poly_eval + 0x3c`): one iteration, then induction on the
remaining count. Generic in the code's address and in the coefficient table. -/

namespace RV

/-- Horner value of a coefficient list, `c₀` first: `c₀ + x (c₁ + x (c₂ + …))`. -/
def polyW (c : List Word) (x : Nat) : Nat := c.foldr (fun a acc => a.toNat + x * acc) 0

theorem polyW_drop (C : List Word) (x j : Nat) (h : j < C.length) :
    polyW (C.drop j) x = C[j].toNat + x * polyW (C.drop (j + 1)) x := by
  rw [List.drop_eq_getElem_cons h]; rfl

/-- One Horner step, modulo `P`. -/
theorem horner_step (s1 s2 acc x c W : Nat) (h2 : s2 % P = (s1 + c) % P) (h1 : s1 % P = (acc * x) % P)
    (h0 : acc % P = W % P) : s2 % P = (c + x * W) % P := by
  have hm : (acc * x) % P = (W * x) % P := by rw [Nat.mul_mod, h0, ← Nat.mul_mod]
  rw [h2, Nat.add_mod, h1, hm, ← Nat.add_mod, Nat.add_comm, Nat.mul_comm]

theorem reg_20_27 (i : Reg) (h1 : 20 ≤ i.toNat) (h2 : i.toNat ≤ 27) :
    i = 20#5 ∨ i = 21#5 ∨ i = 22#5 ∨ i = 23#5 ∨ i = 24#5 ∨ i = 25#5 ∨ i = 26#5 ∨ i = 27#5 := by
  bv_omega

set_option maxHeartbeats 1000000 in
/-- The Horner loop of `poly_eval` placed at any address `A` (callees at their relative offsets), over any table
`C` of field elements at any readable address `T` outside the loop's stack frame; `k` coefficients remain. -/
theorem poly_loop (A T : Word) (C : List Word) (hA : 256 ≤ A.toNat) (hAr : A.toNat + 124 ≤ 4194304)
    (hT : T.toNat + 4 * C.length ≤ 1073741824) (hT4 : T.toNat % 4 = 0) (hC : ∀ i (h : i < C.length), C[i].toNat ≤ P) (k : Nat) :
    ∀ (S : State) (sp0 ra0 v8 v9 v18 v19 x acc : Word),
    1 ≤ k → k ≤ C.length →
    S.pc = A + 60#32 → S.getReg 2#5 = sp0 + 4294967264#32 → S.getReg 9#5 = x → S.getReg 18#5 = BitVec.ofNat 32 k →
    S.getReg 19#5 = T + BitVec.ofNat 32 (4 * (k - 1)) → S.getReg 10#5 = acc →
    acc.toNat ≤ P → acc.toNat % P = polyW (C.drop k) x.toNat % P → x.toNat ≤ P →
    read S.mem (sp0 + 4294967292#32) 4 = ra0 → read S.mem (sp0 + 4294967288#32) 4 = v8 →
    read S.mem (sp0 + 4294967284#32) 4 = v9 → read S.mem (sp0 + 4294967280#32) 4 = v18 →
    read S.mem (sp0 + 4294967276#32) 4 = v19 →
    CodeAt S A Code.poly_eval → CodeAt S (A + 4294967236#32) Code.mul_mod →
    CodeAt S (A + 4294967184#32) Code.add_mod → CodeAt S T C →
    sp0.toNat % 16 = 0 → 4194304 + 48 ≤ sp0.toNat → sp0.toNat ≤ 1073741824 → ra0.toNat % 4 = 0 →
    A.toNat % 4 = 0 → (T.toNat + 4 * C.length + 48 ≤ sp0.toNat ∨ sp0.toNat ≤ T.toNat) →
    ∃ n s', run n S = some s' ∧ s'.pc = ra0 ∧ (s'.getReg 10#5).toNat ≤ P ∧
      (s'.getReg 10#5).toNat % P = polyW C x.toNat % P ∧
      s'.getReg 2#5 = sp0 ∧ s'.getReg 8#5 = v8 ∧ s'.getReg 9#5 = v9 ∧ s'.getReg 18#5 = v18 ∧ s'.getReg 19#5 = v19 ∧
      (∀ i : Reg, 20 ≤ i.toNat → i.toNat ≤ 27 → s'.getReg i = S.getReg i) ∧
      (∀ a : Word, a.toNat + 48 < sp0.toNat ∨ sp0.toNat ≤ a.toNat → s'.mem a = S.mem a) := by
  induction k with
  | zero => intros; omega
  | succ j ih =>
    intro S sp0 ra0 v8 v9 v18 v19 x acc hk1 hk hpc h2 h9 h18 h19 h10 hacc1 hacc2 hx hm1 hm2 hm3 hm4 hm5
      hcode hmul hadd hcoef hsp hlo hhi hra hA4 hTs
    rv_code_facts hcode Code.poly_eval
    rv_steps 3 with hpc, h2, h9, h18, h19, h10
    apply run_callAt (mul_mod_impl (A + 4294967236#32) (by bv_omega))
    · rv_regs
    · intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      subst hc
      rv_codeAt hadd Code.add_mod
    · rv_call_ok hmul Code.mul_mod with h2
    rv_returned S1 hpc1 hpost1 hcs1 hmem1
    simp only [mulModPost] at hpost1
    rv_regs at hpost1
    simp only [h2, h10, Nat.add_sub_cancel] at hpost1 hcs1 hmem1 h19
    rv_steps 2 with hpc1, hcs1, h19, h2, read_of_frame hmem1, table_read hcoef
    apply run_call add_mod_impl
    · rv_call_ok hadd Code.add_mod with hcs1, h2
    rv_returned S2 hpc2 hpost2 hcs2 hmem2 with hcs1, h2
    simp only [addModPost] at hpost2
    rv_regs at hpost2
    rv_steps 1 with hpc2, hcs2, hcs1, h19, h18, read_of_frame hmem2, read_of_frame hmem1
    rcases Nat.eq_zero_or_pos j with hj | hj
    · -- last iteration: fall through to the epilogue
      subst hj
      rv_steps 9 with hpc2, hcs2, hcs1, h19, h18, h2, hm1, hm2, hm3, hm4, hm5, read_of_frame hmem2,
        read_of_frame hmem1
      rv_ret
      have hc0 := hC 0 (by omega)
      obtain ⟨h1a, h1b⟩ := hpost1 (h10 ▸ hacc1) hx
      obtain ⟨h2a, h2b⟩ := hpost2 h1a hc0
      refine ⟨by rv_regs, by rv_regs; exact h2a, ?_, by rv_regs, by rv_regs, by rv_regs, by rv_regs, by rv_regs,
        ?_, by rv_frame with hmem2, hmem1, h2⟩
      · rv_regs
        have e := polyW_drop C x.toNat 0 (by omega)
        rw [List.drop_zero] at e
        rw [e]
        exact horner_step _ _ _ _ _ _ h2b h1b hacc2
      · intro i hi1 hi2
        rcases reg_20_27 i hi1 hi2 with h | h | h | h | h | h | h | h <;> subst h <;>
          simp (disch := rv_callee_saved) only [reduceRSet, next_r, jump_r, hcs2, hcs1, BitVec.reduceEq,
            ite_false]
    · -- loop again: back at the head with one coefficient less
      rv_steps 1 with hpc2, hcs2, hcs1, h19, h18, read_of_frame hmem2, read_of_frame hmem1
      obtain ⟨h1a, h1b⟩ := hpost1 (h10 ▸ hacc1) hx
      obtain ⟨h2a, h2b⟩ := hpost2 h1a (hC j (by omega))
      refine exists_run_mono (ih _ sp0 ra0 v8 v9 v18 v19 x _ hj (by omega) ?_ ?_ ?_ ?_ ?_ rfl ?_ ?_ hx ?_ ?_ ?_ ?_ ?_
        ?_ ?_ ?_ ?_ hsp hlo hhi hra hA4 hTs) ?_
      · rv_regs
      · simp (disch := rv_callee_saved) only [reduceRSet, next_r, jump_r, hcs2, hcs1, BitVec.reduceEq, ite_false, ite_true, h2]
      · simp (disch := rv_callee_saved) only [reduceRSet, next_r, jump_r, hcs2, hcs1, BitVec.reduceEq, ite_false, ite_true, h9]
      · simp (disch := rv_callee_saved) only [reduceRSet, next_r, jump_r, hcs2, hcs1, BitVec.reduceEq, ite_false, ite_true]
        bv_omega
      · rv_regs
        bv_omega
      · rv_regs; exact h2a
      · rv_regs
        rw [polyW_drop C x.toNat j (by omega)]
        exact horner_step _ _ _ _ _ _ h2b h1b hacc2
      all_goals first
        | (simp (disch := rv_disch with h2, hcs1) only [jump_mem, next_mem, set_mem, read_of_frame hmem2,
            read_of_frame hmem1, hm1, hm2, hm3, hm4, hm5]; done)
        | skip
      · rv_codeAt hcode Code.poly_eval with h2
      · rv_codeAt hmul Code.mul_mod with h2
      · rv_codeAt hadd Code.add_mod with h2
      · rv_codeAt hcoef C with h2
      · intro s' ⟨hp, hr10a, hr10b, hr2, hr8, hr9, hr18, hr19, hcsU, hmemU⟩
        refine ⟨hp, hr10a, hr10b, hr2, hr8, hr9, hr18, hr19, fun i hi1 hi2 => (hcsU i hi1 hi2).trans ?_,
          fun a ha => (hmemU a ha).trans ?_⟩
        · rcases reg_20_27 i hi1 hi2 with h | h | h | h | h | h | h | h <;> subst h <;>
            simp (disch := rv_callee_saved) only [reduceRSet, next_r, jump_r, hcs2, hcs1, BitVec.reduceEq,
              ite_false]
        · simp (disch := rv_disch with h2) only [jump_mem, next_mem, set_mem, hmem2, hmem1]

end RV
