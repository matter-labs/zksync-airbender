import Slop.RV.Ext4Call
import Slop.RV.CopyRun
import Slop.RV.Code.ext4_horner

/-! The loop of `ext4_horner` (head at `+0x4c`): one `ext4_mul_add(acc, x, c[k-1])` per iteration, then induction on
the remaining count `k`. Generic in the code's address and in the implementation of `ext4_mul_add` (any code at
`+0xa8` with the `mulAddPre`/`mulAddPost` contract: the plain-Rust and the field-opcode variants). -/

namespace RV
open Spec
set_option maxHeartbeats 400000

/-- From the loop head with `k` coefficients left and `acc` (at `sp0 - 40`) holding `hornerAcc` of the `n - k` done,
to the loop exit (`+0x68`) with `acc` holding all of them. -/
theorem horner_loop (A T X sp0 : Word) (codeM : List Word) (calleesM : List (Word × List Word)) (FM : Nat)
    (hI : ImplementsAtW (A + 168#32) codeM calleesM FM mulAddPre 16 mulAddPost)
    (hA4 : A.toNat % 4 = 0) (hAr : A.toNat + 168 + 4 * codeM.length ≤ 4194304)
    (hcal : ∀ c ∈ calleesM, c.1.toNat + 4 * c.2.length ≤ 4194304)
    (C : ℕ → E4) (x : E4) (n : Nat)
    (hsp : sp0.toNat % 16 = 0) (hlo : 4194304 + 48 + FM ≤ sp0.toNat) (hhi : sp0.toNat ≤ 1073741824)
    (hX4 : X.toNat % 4 = 0) (hXs : sp0.toNat ≤ X.toNat) (hXr : X.toNat + 16 ≤ 1073741824)
    (hT4 : T.toNat % 4 = 0) (hTs : sp0.toNat ≤ T.toNat) (hTr : T.toNat + 16 * n ≤ 1073741824) :
    ∀ k (S : State), 1 ≤ k → k ≤ n →
      CodeAt S A Code.ext4_horner → CodeAt S (A + 168#32) codeM → (∀ c ∈ calleesM, CodeAt S c.1 c.2) →
      S.pc = A + 76#32 → S.getReg 2#5 = sp0 + 4294967248#32 → S.getReg 18#5 = X →
      S.getReg 19#5 = BitVec.ofNat 32 k → S.getReg 20#5 = T + BitVec.ofNat 32 (16 * (k - 1)) →
      canon4 S.mem X → e4At S.mem X = x →
      (∀ i < n, canon4 S.mem (T + BitVec.ofNat 32 (16 * i)) ∧ e4At S.mem (T + BitVec.ofNat 32 (16 * i)) = C i) →
      canon4 S.mem (sp0 + 4294967256#32) → e4At S.mem (sp0 + 4294967256#32) = hornerAcc C x n (n - k) →
      ∃ m S', run m S = some S' ∧ S'.pc = A + 104#32 ∧ S'.getReg 2#5 = sp0 + 4294967248#32 ∧
        canon4 S'.mem (sp0 + 4294967256#32) ∧ e4At S'.mem (sp0 + 4294967256#32) = hornerAcc C x n n ∧
        (∀ i, calleeSaved i → i ≠ 19#5 → i ≠ 20#5 → S'.getReg i = S.getReg i) ∧
        (∀ a : Word, a.toNat + 48 + FM < sp0.toNat ∨ sp0.toNat ≤ a.toNat + 24 → S'.mem a = S.mem a) := by
  intro k
  induction k with
  | zero => intros; omega
  | succ j ih =>
  intro S hk1 hkn hcode hcM hcal' hpc h2 h18 h19 h20 hcX hX hC hcA hA
  rv_code_facts_range hcode Code.ext4_horner 19 26
  rv_steps 5 with hpc, h2, h18, h19, h20
  apply run_callAtW hI
  · rv_regs
  · intro c hc; exact codeAt_mem_eq (by simp only [rv_state]) (hcal' c hc)
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rv_regs; exact codeAt_mem_eq (by simp only [rv_state]) hcM
    all_goals rv_regs
    all_goals try simp only [ROM_END, RAM_END]
    all_goals bv_omega
  · simp only [mulAddPre, argOk, disj16, RAM_END]
    rv_regs
    simp only [rv_state]
    refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ?_, ?_, hcA, hcX, (hC (j + 1 - 1) (by omega)).1⟩
    all_goals bv_omega
  rv_returned S1 hpc1 hpost1 hcs1 hmem1
  simp only [mulAddPost, rv_state] at hpost1
  rv_regs at hpost1
  obtain ⟨hcA1, hA1⟩ := hpost1
  -- what the call left unchanged: `x`, the table, the saved registers
  have hmemX : ∀ p : Word, sp0.toNat ≤ p.toNat → p.toNat + 16 ≤ 1073741824 →
      ∀ a : Word, p.toNat ≤ a.toNat → a.toNat < p.toNat + 16 → S1.mem a = S.mem a := by
    intro p hp1 hp2 a ha1 ha2
    rw [hmem1 a (by rw [h2]; bv_omega) (by bv_omega)]
  have hc := hC (j + 1 - 1) (by omega)
  rw [hX, hc.2, hA] at hA1
  simp only [Nat.add_sub_cancel] at hA1 hc
  have hrom1 : ∀ b : Word, b.toNat < ROM_END → S1.mem b = S.mem b := fun b hb => by
    rw [hmem1 b (by rw [h2]; simp only [ROM_END] at hb; bv_omega) (by simp only [ROM_END] at hb; bv_omega)]
  have hcode1 := codeAt_of_rom hcode (by simp only [Code.ext4_horner, List.length_cons, List.length_nil, ROM_END]; omega) hrom1
  rv_clear_facts
  rv_code_facts_range hcode1 Code.ext4_horner 24 26
  rv_steps 1 with hpc1, hcs1, h20
  have hacc : hornerAcc C x n (n - (j + 1)) * x + C j = hornerAcc C x n (n - j) := by
    have := hornerAcc_step C x n (j + 1) (by omega) hkn; simpa using this
  rw [hacc] at hA1
  have hcsS : ∀ i, calleeSaved i → i ≠ 19#5 → S1.getReg i = S.getReg i := by
    intro i hi h19'
    rw [hcs1 i hi]
    rcases calleeSaved_cases i hi with h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst h <;> first | exact absurd rfl h19' | rv_regs
  have hmemS : ∀ a : Word, a.toNat + 48 + FM < sp0.toNat ∨ sp0.toNat ≤ a.toNat + 24 → S1.mem a = S.mem a := by
    intro a ha; rw [hmem1 a (by rw [h2]; bv_omega) (by bv_omega)]
  rcases Nat.eq_zero_or_pos j with hj | hj
  · subst hj
    rv_steps 1 with hpc1, hcs1, h19
    rv_ret
    refine ⟨by rv_regs; rw [hpc1]; bv_omega, ?_, by simpa only [rv_state] using hcA1, ?_, ?_, ?_⟩
    · rv_regs; rw [hcsS 2#5 (by rv_callee_saved) (by decide), h2]
    · simp only [rv_state]; rw [hA1, Nat.sub_zero]
    · intro i hi h19' h20'; rv_regs
      rw [r_set_miss _ _ _ _ (by rintro rfl; simp [calleeSaved] at hi) h20']
      exact hcsS i hi h19'
    · intro a ha; simp only [rv_state]; exact hmemS a ha
  · rv_steps 1 with hpc1, hcs1, h19
    have hm2 : ∀ a : Word, a.toNat + 48 + FM < sp0.toNat ∨ sp0.toNat ≤ a.toNat + 24 →
        ((S1.setReg 20#5 (T + (BitVec.ofNat 32 (16 * (j + 1 - 1)) + 4294967280#32))).nextInstr.setPC
          (A + 76#32)).mem a = S.mem a := fun a ha => by simp only [rv_state]; exact hmemS a ha
    have hcong : ∀ p : Word, sp0.toNat ≤ p.toNat → p.toNat + 16 ≤ 1073741824 → _ :=
      fun p hp1 hp2 => e4At_congr (m := S.mem) (p := p) (by omega) (fun a ha1 ha2 => hm2 a (by bv_omega))
    refine exists_run_mono (ih _ hj (by omega) (by rv_codeAt hcode1 Code.ext4_horner)
      (codeAt_of_rom hcM (by simp only [ROM_END]; bv_omega) (fun b hb => by simp only [rv_state]; exact hrom1 b hb))
      (fun c hc => codeAt_of_rom (hcal' c hc) (by simp only [ROM_END]; exact hcal c hc)
        (fun b hb => by simp only [rv_state]; exact hrom1 b hb))
      (by rv_regs) (by rv_regs; rw [hcsS 2#5 (by rv_callee_saved) (by decide), h2])
      (by rv_regs; rw [hcsS 18#5 (by rv_callee_saved) (by decide), h18])
      (by rv_regs; rw [hcs1 19#5 (by rv_callee_saved)]; rv_regs; bv_omega)
      (by rv_regs; bv_omega)
      ((hcong X hXs hXr).2.mpr hcX) (by rw [(hcong X hXs hXr).1, hX])
      (fun i hi => ⟨(hcong _ (by bv_omega) (by bv_omega)).2.mpr (hC i hi).1,
        by rw [(hcong _ (by bv_omega) (by bv_omega)).1, (hC i hi).2]⟩)
      (by simpa only [rv_state] using hcA1) (by simp only [rv_state]; rw [hA1])) ?_
    intro S' ⟨hp, h2', hcA', hA', hcs', hm'⟩
    refine ⟨hp, h2', hcA', hA', fun i hi h19' h20' => ?_, fun a ha => (hm' a ha).trans (hm2 a ha)⟩
    rw [hcs' i hi h19' h20']; rv_regs
    rw [r_set_miss _ _ _ _ (by rintro rfl; simp [calleeSaved] at hi) h20']
    exact hcsS i hi h19' 
end RV
