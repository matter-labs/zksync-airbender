import Slop.RV.HornerLoop
import Slop.RV.HornerEpi

/-! `ext4_horner(out, coeffs, n, x)`: `out ← ∑_{i < n} cᵢ xⁱ` (`hornerPost`), for any implementation of `ext4_mul_add`
placed right after it (its only callee): prologue, then the `n = 0` path or the loop (`HornerLoop`), then the
epilogue (`HornerEpi`). -/

namespace RV
open Spec
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false

/-- `ext4_horner` at any address `A`, with an `ext4_mul_add` implementation `codeM` (and its callees) at `A + 0xa8`. -/
theorem ext4_horner_impl (A : Word) (codeM : List Word) (calleesM : List (Word × List Word)) (FM : Nat)
    (hI : ImplementsAtW (A + 168#32) codeM calleesM FM mulAddPre 16 mulAddPost)
    (hAr : A.toNat + 168 + 4 * codeM.length ≤ 4194304)
    (hcal : ∀ c ∈ calleesM, c.1.toNat + 4 * c.2.length ≤ 4194304) :
    ImplementsAtW A Code.ext4_horner ((A + 168#32, codeM) :: calleesM) (48 + FM) hornerPre 16 hornerPost := by
  intro s hentry hcallees hcall hpre
  have hcM : CodeAt s (A + 168#32) codeM := hcallees _ List.mem_cons_self
  have hcal' : ∀ c ∈ calleesM, CodeAt s c.1 c.2 := fun c hc => hcallees c (List.mem_cons_of_mem _ hc)
  clear hcallees
  simp only [hornerPre, argOk, RAM_END] at hpre
  obtain ⟨⟨ho4, hos, hor⟩, ⟨hX4, hXs, hXr⟩, hcX, hT4, hTs, hTr, hC⟩ := hpre
  rw [Call, hentry] at hcall
  unfold ReturnsW
  rv_start Code.ext4_horner hcall
  rv_steps 13 with hentry
  rcases (by bv_omega : s.getReg 12#5 = 0#32 ∨ 1 ≤ (s.getReg 12#5).toNat) with hn | hn
  · rv_steps 1 with hentry
    rv_name W hW
    have hWm : ∀ a : Word, (s.getReg 2#5).toNat ≤ a.toNat → W.mem a = s.mem a := by
      intro a ha; rw [← hW]
      simp (disch := first | assumption | bv_omega) only [rv_state, write_outside]
    have hWrom : ∀ b : Word, b.toNat < ROM_END → W.mem b = s.mem b := by
      intro b hb; rw [← hW]
      simp (disch := first | assumption | (simp only [writable, ROM_END, RAM_END] at *; bv_omega)) only [rv_state, write_rom]
    have hW1 : read W.mem (s.getReg 2#5 + 4294967292#32) 4 = s.getReg 1#5 := by
      rw [← hW]; simp (disch := rv_disch) only [rv_state, BitVec.reduceAdd, read_write_same4, read_write_off, read_write_off0r]
    have hW8 : read W.mem (s.getReg 2#5 + 4294967288#32) 4 = s.getReg 8#5 := by
      rw [← hW]; simp (disch := rv_disch) only [rv_state, BitVec.reduceAdd, read_write_same4, read_write_off, read_write_off0r]
    have hW9 : read W.mem (s.getReg 2#5 + 4294967284#32) 4 = s.getReg 9#5 := by
      rw [← hW]; simp (disch := rv_disch) only [rv_state, BitVec.reduceAdd, read_write_same4, read_write_off, read_write_off0r]
    have hW18 : read W.mem (s.getReg 2#5 + 4294967280#32) 4 = s.getReg 18#5 := by
      rw [← hW]; simp (disch := rv_disch) only [rv_state, BitVec.reduceAdd, read_write_same4, read_write_off, read_write_off0r]
    have hW19 : read W.mem (s.getReg 2#5 + 4294967276#32) 4 = s.getReg 19#5 := by
      rw [← hW]; simp (disch := rv_disch) only [rv_state, BitVec.reduceAdd, read_write_same4, read_write_off, read_write_off0r]
    have hW20 : read W.mem (s.getReg 2#5 + 4294967272#32) 4 = s.getReg 20#5 := by
      rw [← hW]; simp (disch := rv_disch) only [rv_state, BitVec.reduceAdd, read_write_same4, read_write_off, read_write_off0r]
    refine run_cont (horner_epi A (s.getReg 2#5) (s.getReg 10#5) _ _ _ _ _ _ W hpc (by omega)
      (codeAt_of_rom hcode (by simp only [Code.ext4_horner, List.length_cons, List.length_nil, ROM_END]; omega) hWrom)
      (by rw [← hW]; rv_regs; try rw [hentry]) (by rw [← hW]; rv_regs) (by rw [← hW]; rv_regs)
      hsp (by omega) hhi ho4 hos hor hra hW1 hW8 hW9 hW18 hW19 hW20) ?_
    intro S'' ⟨hpc'', h2'', h8'', h9'', h18'', h19'', h20'', hcs'', hcA'', hA'', hm''⟩
    have hacc : canon4 W.mem (s.getReg 2#5 + 4294967256#32) ∧ e4At W.mem (s.getReg 2#5 + 4294967256#32) = 0 := by
      rw [← hW]; simp only [canon4, e4At]
      simp (disch := rv_disch) only [rv_state, BitVec.reduceAdd, read_write_same4, read_write_off, read_write_off0r,
        read_write_disjoint]
      exact ⟨by decide, e4_zero⟩
    have h0 : (s.getReg 12#5).toNat = 0 := by rw [hn]; rfl
    refine ⟨0, S'', rfl, hpc'', ⟨hcA'' hacc.1, by rw [hA'', hacc.2, h0, Finset.range_zero, Finset.sum_empty]⟩, ?_, ?_⟩
    · have hhi : ∀ i : Reg, 21 ≤ i.toNat → i.toNat ≤ 27 → S''.getReg i = s.getReg i := by
        intro i h1 h2
        rw [hcs'' i h1 h2, ← hW]
        rcases (by bv_omega : i = 21#5 ∨ i = 22#5 ∨ i = 23#5 ∨ i = 24#5 ∨ i = 25#5 ∨ i = 26#5 ∨ i = 27#5) with
          h|h|h|h|h|h|h <;> subst h <;> rv_regs
      intro i hi
      rcases calleeSaved_cases i hi with h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst h
      all_goals first | assumption | exact hhi _ (by decide) (by decide)
    · intro a ha hb
      rw [hm'' a hb]
      rcases ha with ha | ha
      · rw [← hW]; simp (disch := rv_disch) only [rv_state, write_outside]
      · exact hWm a ha
  · rv_steps 6 with hentry
    rv_name U hU
    -- memory at or above `sp` is as at entry; ROM too
    have hUm : ∀ a : Word, (s.getReg 2#5).toNat ≤ a.toNat → U.mem a = s.mem a := by
      intro a ha; rw [← hU]
      simp (disch := first | assumption | bv_omega) only [rv_state, write_outside]
    have hUrom : ∀ b : Word, b.toNat < ROM_END → U.mem b = s.mem b := by
      intro b hb; rw [← hU]
      simp (disch := first | assumption | (simp only [writable, ROM_END, RAM_END] at *; bv_omega)) only [rv_state, write_rom]
    have hcU : ∀ p : Word, (s.getReg 2#5).toNat ≤ p.toNat → p.toNat + 16 ≤ 1073741824 → _ :=
      fun p hp1 hp2 => e4At_congr (m := s.mem) (m' := U.mem) (p := p) (by omega) (fun a ha1 ha2 => hUm a (by omega))
    have hn' : (s.getReg 12#5).toNat ≤ 67108864 := by omega
    refine run_cont (horner_loop A (s.getReg 11#5) (s.getReg 13#5) (s.getReg 2#5) codeM calleesM FM hI hpc hAr hcal
      (fun i => e4At s.mem (s.getReg 11#5 + BitVec.ofNat 32 (16 * i))) (e4At s.mem (s.getReg 13#5))
      (s.getReg 12#5).toNat hsp (by omega) hhi hX4 hXs hXr hT4 hTs hTr
      (s.getReg 12#5).toNat U hn le_rfl (codeAt_of_rom hcode (by simp only [Code.ext4_horner, List.length_cons, List.length_nil, ROM_END]; omega) hUrom)
      (codeAt_of_rom hcM (by simp only [ROM_END]; bv_omega) hUrom)
      (fun c hc => codeAt_of_rom (hcal' c hc) (by simp only [ROM_END]; exact hcal c hc) hUrom)
      (by rw [← hU]; rv_regs; rw [hentry]) (by rw [← hU]; rv_regs) (by rw [← hU]; rv_regs) (by rw [← hU]; rv_regs; simp)
      (by rw [← hU]; rv_regs; bv_omega)
      ((hcU _ hXs hXr).2.mpr hcX) (hcU _ hXs hXr).1
      (fun i hi => ⟨(hcU _ (by bv_omega) (by bv_omega)).2.mpr (hC i hi), (hcU _ (by bv_omega) (by bv_omega)).1⟩)
      ?_ ?_) ?_
    · rw [← hU]; simp only [canon4]
      simp (disch := rv_disch) only [rv_state, BitVec.reduceAdd, read_write_same4, read_write_off, read_write_off0r, read_write_disjoint]
      decide
    · rw [← hU, Nat.sub_self]; simp only [e4At, hornerAcc]
      simp (disch := rv_disch) only [rv_state, BitVec.reduceAdd, read_write_same4, read_write_off, read_write_off0r, read_write_disjoint]
      exact e4_zero
    intro S' ⟨hpc', h2', hcA', hA', hcs', hm'⟩
    have hS'rom : ∀ b : Word, b.toNat < ROM_END → S'.mem b = s.mem b := fun b hb => by
      rw [hm' b (by simp only [ROM_END] at hb; omega), hUrom b hb]
    have hcode' := codeAt_of_rom hcode (by simp only [Code.ext4_horner, List.length_cons, List.length_nil, ROM_END]; omega)
      hS'rom
    -- the saved registers, still in the frame
    have hsv : ∀ k : Word, 24 ≤ k.toNat → k.toNat ≤ 44 → read S'.mem (s.getReg 2#5 + 4294967248#32 + k) 4 =
        read U.mem (s.getReg 2#5 + 4294967248#32 + k) 4 := fun k hk1 hk2 => by
      apply read_congr; intro j hj; apply hm'; right; bv_omega
    have hU1 : read S'.mem (s.getReg 2#5 + 4294967292#32) 4 = s.getReg 1#5 := by
      have := hsv 44#32 (by decide) (by decide); simp only [BitVec.add_assoc, BitVec.reduceAdd] at this; rw [this, ← hU]
      simp (disch := rv_disch) only [rv_state, BitVec.reduceAdd, read_write_same4, read_write_off, read_write_off0r]
    have hU8 : read S'.mem (s.getReg 2#5 + 4294967288#32) 4 = s.getReg 8#5 := by
      have := hsv 40#32 (by decide) (by decide); simp only [BitVec.add_assoc, BitVec.reduceAdd] at this; rw [this, ← hU]
      simp (disch := rv_disch) only [rv_state, BitVec.reduceAdd, read_write_same4, read_write_off, read_write_off0r]
    have hU9 : read S'.mem (s.getReg 2#5 + 4294967284#32) 4 = s.getReg 9#5 := by
      have := hsv 36#32 (by decide) (by decide); simp only [BitVec.add_assoc, BitVec.reduceAdd] at this; rw [this, ← hU]
      simp (disch := rv_disch) only [rv_state, BitVec.reduceAdd, read_write_same4, read_write_off, read_write_off0r]
    have hU18 : read S'.mem (s.getReg 2#5 + 4294967280#32) 4 = s.getReg 18#5 := by
      have := hsv 32#32 (by decide) (by decide); simp only [BitVec.add_assoc, BitVec.reduceAdd] at this; rw [this, ← hU]
      simp (disch := rv_disch) only [rv_state, BitVec.reduceAdd, read_write_same4, read_write_off, read_write_off0r]
    have hU19 : read S'.mem (s.getReg 2#5 + 4294967276#32) 4 = s.getReg 19#5 := by
      have := hsv 28#32 (by decide) (by decide); simp only [BitVec.add_assoc, BitVec.reduceAdd] at this; rw [this, ← hU]
      simp (disch := rv_disch) only [rv_state, BitVec.reduceAdd, read_write_same4, read_write_off, read_write_off0r]
    have hU20 : read S'.mem (s.getReg 2#5 + 4294967272#32) 4 = s.getReg 20#5 := by
      have := hsv 24#32 (by decide) (by decide); simp only [BitVec.add_assoc, BitVec.reduceAdd] at this; rw [this, ← hU]
      simp (disch := rv_disch) only [rv_state, BitVec.reduceAdd, read_write_same4, read_write_off, read_write_off0r]
    have h9' : S'.getReg 9#5 = s.getReg 10#5 := by rw [hcs' 9#5 (by rv_callee_saved) (by decide) (by decide), ← hU]; rv_regs
    refine run_cont (horner_epi A (s.getReg 2#5) (s.getReg 10#5) _ _ _ _ _ _ S' hpc (by omega) hcode' hpc' h2' h9'
      hsp (by omega) hhi ho4 hos hor hra hU1 hU8 hU9 hU18 hU19 hU20) ?_
    intro S'' ⟨hpc'', h2'', h8'', h9'', h18'', h19'', h20'', hcs'', hcA'', hA'', hm''⟩
    refine ⟨0, S'', rfl, hpc'', ⟨hcA'' hcA', by rw [hA'', hA', hornerAcc_full]⟩, ?_, ?_⟩
    · have hhi : ∀ i : Reg, 21 ≤ i.toNat → i.toNat ≤ 27 → S''.getReg i = s.getReg i := by
        intro i h1 h2
        rw [hcs'' i h1 h2, hcs' i (by unfold calleeSaved; bv_omega) (by bv_omega) (by bv_omega), ← hU]
        rcases (by bv_omega : i = 21#5 ∨ i = 22#5 ∨ i = 23#5 ∨ i = 24#5 ∨ i = 25#5 ∨ i = 26#5 ∨ i = 27#5) with
          h|h|h|h|h|h|h <;> subst h <;> rv_regs
      intro i hi
      rcases calleeSaved_cases i hi with h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst h
      all_goals first | assumption | exact hhi _ (by decide) (by decide)
    · intro a ha hb
      rw [hm'' a hb, hm' a (by omega)]
      rcases ha with ha | ha
      · rw [← hU]; simp (disch := rv_disch) only [rv_state, write_outside]
      · exact hUm a ha
end RV
