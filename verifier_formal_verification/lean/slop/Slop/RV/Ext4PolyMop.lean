import Slop.RV.Horner
import Slop.RV.MulAddMop
import Slop.RV.Coeffs4
import Slop.RV.Code.ext4_poly_mop

/-! `ext4_poly(out, y)` with the field opcodes: `y` to Montgomery form (`mul` by `R²`), `ext4_horner` over
`COEFFS4`, back to canonical form (`mul` by 1). -/

namespace RV
open Spec
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false

/-- `ext4_poly` (feature `mop`) at `A`, with `ext4_horner` at `A - 0x16c` and its `ext4_mul_add` after it. -/
theorem ext4_poly_mop_impl (A : Word) (hA : 0x16c ≤ A.toNat) (hAr : A.toNat + 0xc0 ≤ 4194304) :
    ImplementsAtW A Code.ext4_poly_mop [(A + 4294966932#32, Code.ext4_horner),
      (A + 4294966932#32 + 168#32, Code.ext4_mul_add_mop)] 112 e4polyPre 16 e4polyPost := by
  intro s hentry hcallees hcall hpre
  have hcH := hcallees (A + 4294966932#32, Code.ext4_horner) (.head _)
  have hcM := hcallees (A + 4294966932#32 + 168#32, Code.ext4_mul_add_mop) (.tail _ (.head _))
  dsimp only at hcH hcM
  clear hcallees
  simp only [e4polyPre, argOk, RAM_END] at hpre
  obtain ⟨⟨ho4, hos, hor⟩, ⟨hy4, hys, hyr⟩, hcy, htab, hspT⟩ := hpre
  rw [Call, hentry] at hcall
  unfold ReturnsW
  rv_start Code.ext4_poly_mop hcall
  rv_steps 30 with hentry
  rv_name U hU
  have hUm : ∀ a : Word, (s.getReg 2#5).toNat ≤ a.toNat → U.mem a = s.mem a := by
    intro a ha; rw [← hU]
    simp (disch := first | assumption | bv_omega) only [rv_state, write_outside]
  have hUrom : ∀ b : Word, b.toNat < ROM_END → U.mem b = s.mem b := by
    intro b hb; rw [← hU]
    simp (disch := first | assumption | (simp only [writable, ROM_END, RAM_END] at *; bv_omega)) only [rv_state, write_rom]
  have htabU : CodeMem U.mem 0x1400190#32 Code.COEFFS4 := fun i hi => by
    rw [read_congr U.mem s.mem _ 4 (fun j hj => hUm _ (by rw [coeffs4_length] at hi; bv_omega))]; exact htab i hi
  have u2 : U.getReg 2#5 = s.getReg 2#5 + 4294967248#32 := by rw [← hU]; rv_regs
  have u10 : U.getReg 10#5 = s.getReg 2#5 + 4294967268#32 := by rw [← hU]; rv_regs
  have u11 : U.getReg 11#5 = 20971920#32 := by rw [← hU]; rv_regs
  have u12 : U.getReg 12#5 = 32#32 := by rw [← hU]; rv_regs
  have u13 : U.getReg 13#5 = s.getReg 2#5 + 4294967252#32 := by rw [← hU]; rv_regs
  apply run_callAtW (ext4_horner_impl (A + 4294966932#32) Code.ext4_mul_add_mop [] 16
    (ext4_mul_add_mop_impl _) (by simp only [Code.ext4_mul_add_mop, List.length_cons, List.length_nil]; bv_omega)
    (by simp))
  · rw [← hU]; rv_regs
  · intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    subst hc
    exact codeAt_of_rom hcM (by simp only [Code.ext4_mul_add_mop, List.length_cons, List.length_nil, ROM_END]; bv_omega) hUrom
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [← hU] <;> rv_regs
    · rw [hU]; exact codeAt_of_rom hcH (by simp only [Code.ext4_horner, List.length_cons, List.length_nil, ROM_END]; bv_omega) hUrom
    all_goals try simp only [ROM_END, RAM_END, Code.ext4_horner, List.length_cons, List.length_nil]
    all_goals bv_omega
  · simp only [hornerPre, argOk, RAM_END, u2, u10, u11, u12, u13]
    refine ⟨⟨by bv_omega, by bv_omega, by bv_omega⟩, ⟨by bv_omega, by bv_omega, by bv_omega⟩, ?_, by decide,
      by bv_omega, by decide, fun i hi => (table4 htabU i (by simpa using hi)).1⟩
    rw [← hU]; simp only [canon4]
    simp (disch := rv_disch) only [rv_state, BitVec.reduceAdd, read_write_same4, read_write_off, read_write_off0r,
      read_write_disjoint]
    exact ⟨mopVal_lt _ _ _ _ nofun, mopVal_lt _ _ _ _ nofun, mopVal_lt _ _ _ _ nofun, mopVal_lt _ _ _ _ nofun⟩
  rv_returned S1 hpc1 hpost1 hcs1 hmem1
  simp only [hornerPost, u10, u11, u12, u13] at hpost1
  obtain ⟨hcA1, hA1⟩ := hpost1
  -- the value of `yy` (Montgomery form of `y`) and of the table
  have hyy : e4At U.mem (s.getReg 2#5 + 4294967252#32) = limbsAt s.mem (s.getReg 11#5) := by
    rw [← hU]; simp only [e4At, limbsAt, e4]
    simp (disch := rv_disch) only [rv_state, BitVec.reduceAdd, read_write_same4, read_write_off, read_write_off0r,
      read_write_disjoint, mont_new]
  rw [hyy, show (32#32 : Word).toNat = 32 from rfl,
    Finset.sum_congr rfl (fun i hi => by rw [(table4 htabU i (Finset.mem_range.mp hi)).2])] at hA1
  have hS1rom : ∀ b : Word, b.toNat < ROM_END → S1.mem b = s.mem b := fun b hb => by
    rw [hmem1 b (by rw [u2]; simp only [ROM_END] at hb; bv_omega) (by rw [u10]; simp only [ROM_END] at hb; bv_omega), hUrom b hb]
  have hcode1 := codeAt_of_rom hcode (by simp only [Code.ext4_poly_mop, List.length_cons, List.length_nil, ROM_END]; omega) hS1rom
  have hsv : ∀ k : Word, 36 ≤ k.toNat → k.toNat ≤ 44 → read S1.mem (s.getReg 2#5 + 4294967248#32 + k) 4 =
      read U.mem (s.getReg 2#5 + 4294967248#32 + k) 4 := fun k hk1 hk2 => by
    apply read_congr; intro j hj; apply hmem1
    · rw [u2]; right; bv_omega
    · rw [u10]; right; bv_omega
  have h1' : read S1.mem (s.getReg 2#5 + 4294967292#32) 4 = s.getReg 1#5 := by
    have := hsv 44#32 (by decide) (by decide); simp only [BitVec.add_assoc, BitVec.reduceAdd] at this; rw [this, ← hU]
    simp (disch := rv_disch) only [rv_state, BitVec.reduceAdd, read_write_same4, read_write_off, read_write_off0r]
  have h8' : read S1.mem (s.getReg 2#5 + 4294967288#32) 4 = s.getReg 8#5 := by
    have := hsv 40#32 (by decide) (by decide); simp only [BitVec.add_assoc, BitVec.reduceAdd] at this; rw [this, ← hU]
    simp (disch := rv_disch) only [rv_state, BitVec.reduceAdd, read_write_same4, read_write_off, read_write_off0r]
  have h9' : read S1.mem (s.getReg 2#5 + 4294967284#32) 4 = s.getReg 9#5 := by
    have := hsv 36#32 (by decide) (by decide); simp only [BitVec.add_assoc, BitVec.reduceAdd] at this; rw [this, ← hU]
    simp (disch := rv_disch) only [rv_state, BitVec.reduceAdd, read_write_same4, read_write_off, read_write_off0r]
  have s2 : S1.getReg 2#5 = s.getReg 2#5 + 4294967248#32 := by rw [hcs1 _ (by rv_callee_saved), u2]
  have s9 : S1.getReg 9#5 = s.getReg 10#5 := by rw [hcs1 _ (by rv_callee_saved), ← hU]; rv_regs
  rv_clear_facts
  rv_code_facts_range hcode1 Code.ext4_poly_mop 30 48
  have p1 : S1.pc = A + 120#32 := by rw [hpc1, ← hU]; rv_regs
  rv_steps 18 with p1, s2, s9, h1', h8', h9'
  rv_ret
  refine ⟨by rv_regs, ?_, ?_, ?_⟩
  · simp only [e4polyPost, canon4, limbsAt]
    simp (disch := rv_disch) only [rv_state, BitVec.reduceAdd, read_write_same4, read_write_off, read_write_off0r,
      read_write_off0l, read_write_disjoint, mul_one_val]
    refine ⟨⟨mopVal_lt _ _ _ _ nofun, mopVal_lt _ _ _ _ nofun, mopVal_lt _ _ _ _ nofun, mopVal_lt _ _ _ _ nofun⟩, ?_⟩
    simp only [e4At, e4, BitVec.add_assoc, BitVec.reduceAdd] at hA1
    rw [hA1, poly4]; rfl
  · intro i hi
    rcases calleeSaved_cases i hi with h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst h <;> rv_regs <;>
      first | rfl | (rw [s2]; bv_omega) | (rw [hcs1 _ (by rv_callee_saved), ← hU]; rv_regs)
  · intro a ha hb
    simp (disch := rv_disch) only [rv_state, write_outside]
    rw [hmem1 a (by rw [u2]; bv_omega) (by rw [u10]; bv_omega)]
    rcases ha with ha | ha
    · rw [← hU]; simp (disch := rv_disch) only [rv_state, write_outside]
    · exact hUm a ha
end RV
