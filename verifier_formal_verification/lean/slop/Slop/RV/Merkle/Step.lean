import Slop.RV.Tactic
import Slop.RV.CallW
import Slop.RV.CopyRun
import Slop.RV.Merkle.Block
import Slop.RV.Jal
import Human.SpecMerkle

/-! `merkle_step(st, right, sib)`: one level of a Merkle path, the node in `st.state` and the sibling at `sib` into
the parent (`Spec.hash2`): the side branch (by steps), the block (`merkle_block`), a tail call of
`blake2s_compress`. -/

namespace RV
open Spec
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- The parent of the node at `a0` (`st.state`) and the sibling at `a2` (`a1 ≠ 0`: the node is the right child). -/
def merklePost (s s' : State) : Prop :=
  readWords s'.mem (s.getReg 10#5) 8 =
    if s.getReg 11#5 ≠ 0 then hash2 (readWords s.mem (s.getReg 12#5) 8) (readWords s.mem (s.getReg 10#5) 8)
    else hash2 (readWords s.mem (s.getReg 10#5) 8) (readWords s.mem (s.getReg 12#5) 8)

/-- The evaluator (`len` bytes, `al`-aligned) in RAM above `sp`, the sibling (8 words) in RAM above `sp`, outside
it. -/
def merklePre (al len : Nat) (s : State) : Prop :=
  (s.getReg 10#5).toNat % al = 0 ∧ (s.getReg 2#5).toNat ≤ (s.getReg 10#5).toNat ∧
  (s.getReg 10#5).toNat + len ≤ RAM_END ∧ (s.getReg 12#5).toNat % 4 = 0 ∧
  (s.getReg 2#5).toNat ≤ (s.getReg 12#5).toNat ∧ (s.getReg 12#5).toNat + 32 ≤ RAM_END ∧
  ((s.getReg 12#5).toNat + 32 ≤ (s.getReg 10#5).toNat ∨ (s.getReg 10#5).toNat + len ≤ (s.getReg 12#5).toNat)

theorem setReg0_getReg (T : State) (v : Word) (r : Reg) : (T.setReg 0#5 v).getReg r = T.getReg r := by
  unfold State.getReg State.setReg
  by_cases h : r = 0
  · simp [h]
  · have h' : ¬ r = 0#5 := h
    simp only [h, h', ite_false]

theorem setPC_getReg' (T : State) (t : Word) (r : Reg) : (T.setPC t).getReg r = T.getReg r := rfl
theorem setPC_setReg_mem (T : State) (t v : Word) (r : Reg) : ((T.setPC t).setReg r v).mem = T.mem := rfl

/-- From word 9 (the halves' pointers `L`, `R` in `a1`, `a2`): the block, the tail call, the return to `s`'s `ra`
with the hash of the halves at `a0`. -/
theorem merkle_from9 (A : Word) (s S : State) (L R : Word)
    (hal : A.toNat % 4 = 0) (hrom : A.toNat + 4 * 72 ≤ ROM_END)
    (hAbr : (A + 284#32 + 0xFFFFDB7C#32).toNat + 4 * Code.blake2s_compress.length ≤ ROM_END)
    (hcode : CodeAt S A Code.merkle_step) (hbl : CodeAt S (A + 284#32 + 0xFFFFDB7C#32) Code.blake2s_compress)
    (hpc : S.pc = A + 36#32) (h2 : S.getReg 2#5 = s.getReg 2#5 + 4294967280#32) (h10 : S.getReg 10#5 = s.getReg 10#5)
    (h11 : S.getReg 11#5 = L) (h12 : S.getReg 12#5 = R)
    (hra : read S.mem (S.getReg 2#5 + 12#32) 4 = s.getReg 1#5) (hs0 : read S.mem (S.getReg 2#5 + 8#32) 4 = s.getReg 8#5)
    (hcs : ∀ r : Reg, calleeSaved r → r ≠ 2#5 → r ≠ 8#5 → S.getReg r = s.getReg r)
    (hmem : ∀ a : Word, a.toNat + 8 < (s.getReg 2#5).toNat ∨ (s.getReg 2#5).toNat ≤ a.toNat → S.mem a = s.mem a)
    (hra4 : (s.getReg 1#5).toNat % 4 = 0) (hsp : (s.getReg 2#5).toNat % 16 = 0)
    (hsp1 : ROM_END + 160 ≤ (s.getReg 2#5).toNat)
    (ha4 : (s.getReg 10#5).toNat % 4 = 0) (hspa : (s.getReg 2#5).toNat ≤ (s.getReg 10#5).toNat)
    (hR : (s.getReg 10#5).toNat + 132 ≤ RAM_END)
    (hL4 : L.toNat % 4 = 0) (hL1 : (s.getReg 2#5).toNat ≤ L.toNat) (hL2 : L.toNat + 32 ≤ RAM_END)
    (hR4 : R.toNat % 4 = 0) (hR1 : (s.getReg 2#5).toNat ≤ R.toNat) (hR2 : R.toNat + 32 ≤ RAM_END)
    (hRd : R.toNat + 32 ≤ (s.getReg 10#5).toNat + 64 ∨ (s.getReg 10#5).toNat + 96 ≤ R.toNat) :
    ∃ m t, run m S = some t ∧ t.pc = s.getReg 1#5 ∧
      readWords t.mem (s.getReg 10#5) 8 = hash2 (readWords s.mem L 8) (readWords s.mem R 8) ∧
      (∀ i, calleeSaved i → t.getReg i = s.getReg i) ∧
      (∀ a : Word, a.toNat + 160 < (s.getReg 2#5).toNat ∨ (s.getReg 2#5).toNat ≤ a.toNat →
        a.toNat < (s.getReg 10#5).toNat ∨ (s.getReg 10#5).toNat + 132 ≤ a.toNat → t.mem a = s.mem a) := by
  simp only [ROM_END, RAM_END] at *
  have hspn : (S.getReg 2#5).toNat = (s.getReg 2#5).toNat - 16 := by rw [h2]; bv_omega
  obtain ⟨S', hrun, hpc', r10, r11, r12, r1, r8, r2, rcs, hiv, hblk, hct, hfr, hromB⟩ :=
    merkle_block S A hal (by simp only [ROM_END]; rw [show Code.merkle_step.length = 72 from rfl]; omega) hcode hpc
      (by omega) (by simp only [ROM_END]; omega) (by rw [h10]; exact ha4) (by rw [h10]; omega)
      (by rw [h10]; simp only [RAM_END]; omega) (by rw [h11]; exact hL4) (by rw [h11]; simp only [ROM_END]; omega)
      (by rw [h11]; simp only [RAM_END]; omega) (by rw [h12]; exact hR4) (by rw [h12]; simp only [ROM_END]; omega)
      (by rw [h12]; simp only [RAM_END]; omega) (by rw [h10, h12]; omega)
  -- the tail call `jal x0, blake2s_compress`
  set Ab := A + 284#32 + 0xFFFFDB7C#32 with hAb
  have hfetch : read S'.mem S'.pc 4 = 0xb7dfd06f#32 := by
    rw [hpc', read_congr S'.mem S.mem _ 4 (fun j hj => hromB _ (by simp only [ROM_END]; bv_omega))]
    have hw : ∀ h : 71 < Code.merkle_step.length, Code.merkle_step[71]'h = 0xb7dfd06f#32 := by decide +kernel
    exact (hcode 71 (by rw [show Code.merkle_step.length = 72 from rfl]; omega)).trans (hw _)
  have hstep : step S' = some ((S'.setPC Ab).setReg 0#5 (S'.pc + 4)) := by
    rw [step_fetch S' _ (by rw [hpc']; bv_omega) (by rw [hpc']; simp only [ROM_END]; bv_omega) hfetch,
      show decode 0xb7dfd06f#32 = some (.jal 0#5 0xFFFFDB7C#32) by decide +kernel, Option.bind_some,
      exec_jal _ _ _ (by rw [hpc']; simp only [hAb] at hAbr ⊢; bv_omega), hpc']
  obtain ⟨X, hX⟩ : ∃ X, X = (S'.setPC Ab).setReg 0#5 (S'.pc + 4) := ⟨_, rfl⟩
  rw [← hX] at hstep
  have xr : ∀ r : Reg, X.getReg r = S'.getReg r := fun r => by rw [hX, setReg0_getReg, setPC_getReg']
  have xm : X.mem = S'.mem := by rw [hX, setPC_setReg_mem]
  have xsp : X.getReg 2#5 = s.getReg 2#5 := by rw [xr, r2, h2]; bv_omega
  have xrom : ∀ b : Word, b.toNat < ROM_END → X.mem b = S.mem b := fun b hb => by rw [xm, hromB b hb]
  have xpc : X.pc = Ab := by rw [hX]; rfl
  obtain ⟨n, U, hrunU, hpcU, hpost, hcsU, hmemU⟩ := blake2s_compress_impl Ab X xpc (by simp)
    ⟨by rw [xpc]; exact codeAt_of_rom hbl hAbr xrom,
      by rw [xpc]; simp only [hAb]; bv_omega,
      by rw [xpc]; simp only [ROM_END]; omega,
      by show (X.getReg 1#5).toNat % 4 = 0; rw [xr, r1, hra]; exact hra4,
      by show (X.getReg 2#5).toNat % 16 = 0; rw [xsp]; exact hsp,
      by show ROM_END + 160 ≤ (X.getReg 2#5).toNat; rw [xsp]; simp only [ROM_END]; omega,
      by show (X.getReg 2#5).toNat ≤ RAM_END; rw [xsp]; simp only [RAM_END]; omega⟩
    (by simp only [blakePre, xsp, xr, r10, r12, h10, RAM_END]; exact ⟨ha4, hspa, hR, Or.inr trivial⟩)
  replace hcsU : ∀ i, calleeSaved i → U.getReg i = X.getReg i := hcsU
  replace hmemU : ∀ a : Word, a.toNat + 160 < (X.getReg 2#5).toNat ∨ (X.getReg 2#5).toNat ≤ a.toNat →
      a.toNat < (X.getReg 10#5).toNat ∨ (X.getReg 10#5).toNat + 132 ≤ a.toNat → U.mem a = X.mem a := hmemU
  simp only [blakePost, xr, r10, r11, r12, h10] at hpost
  -- the halves, read where `merkle_check` put them: untouched by the prologue's two stack words
  have hhalf : ∀ P : Word, (s.getReg 2#5).toNat ≤ P.toNat → P.toNat + 32 ≤ 1073741824 →
      wordsAt S.mem P 8 = readWords s.mem P 8 := fun P h1 h2' => by
    apply Vector.ext; intro i hi
    simp only [wordsAt, readWords, Vector.getElem_ofFn]
    exact read_congr _ _ _ _ (fun j hj => hmem _ (by right; bv_omega))
  refine ⟨_, U, run_trans (run_trans hrun (show run 1 S' = some X by rw [run_succ, hstep]; rfl)) hrunU, ?_, ?_, fun i hi => ?_,
    fun a ha hb => ?_⟩
  · rw [hpcU]; show X.getReg 1#5 = _; rw [xr, r1, hra]
  · show wordsAt U.mem (s.getReg 10#5) 8 = _
    rw [hpost.1, xm, ← h10, hiv, hblk, hct, h11, h12, hhalf L hL1 hL2, hhalf R hR1 hR2]
    rfl
  · rw [hcsU i hi, xr]
    by_cases i2 : i = 2#5
    · subst i2; rw [r2, h2]; bv_omega
    by_cases i8 : i = 8#5
    · subst i8; rw [r8, hs0]
    rw [rcs i hi i2 i8, hcs i hi i2 i8]
  · rw [hmemU a (by rw [xsp]; exact ha) (by rw [xr, r10, h10]; exact hb), xm,
      hfr a (by rw [h10]; exact hb), hmem a (by omega)]

theorem merkle_step_impl (A : Word)
    (hAbr : (A + 284#32 + 0xFFFFDB7C#32).toNat + 4 * Code.blake2s_compress.length ≤ ROM_END) :
    ImplementsAtW A Code.merkle_step [(A + 284#32 + 0xFFFFDB7C#32, Code.blake2s_compress)] 160 (merklePre 4 132) 132
      merklePost := by
  intro s hentry hcal hcall hpre
  have hbl := hcal _ List.mem_cons_self
  have hcall' := hcall
  unfold ReturnsW
  rw [Call, hentry] at hcall
  obtain ⟨ha4, hspa, hR, hs4, hs1, hs2, hsd⟩ := hpre
  simp only [RAM_END] at hR hs2
  rv_start Code.merkle_step hcall
  simp only [Nat.reduceAdd, Nat.reduceMul] at hrom
  by_cases hr : s.getReg 11#5 = 0
  · rv_steps 4 with hentry
    apply run_of_step
    rv_step_simp with hentry
    rv_steps 1
    rv_cut
    have srom : ∀ b : Word, b.toNat < ROM_END → S.mem b = s.mem b := fun b hb => by
      simp only [ROM_END] at hb
      rw [cut_mem]
      repeat rw [write_outside (h := Or.inl (by bv_omega)) (ha := by bv_omega)]
    have hmem : ∀ a : Word, a.toNat + 8 < (s.getReg 2#5).toNat ∨ (s.getReg 2#5).toNat ≤ a.toNat →
        S.mem a = s.mem a := fun a ha => by
      rw [cut_mem]
      repeat rw [write_outside (h := by bv_omega) (ha := by bv_omega)]
    have hra' : read S.mem (S.getReg 2#5 + 12#32) 4 = s.getReg 1#5 := by
      rw [cut_mem, cut_r2, read_write_disjoint (h := by bv_omega) (ha := by bv_omega) (hc := by bv_omega),
        show s.getReg 2#5 + 4294967280#32 + 12#32 = s.getReg 2#5 + 4294967292#32 by bv_omega, read_write_same4]
    have hs0' : read S.mem (S.getReg 2#5 + 8#32) 4 = s.getReg 8#5 := by
      rw [cut_mem, cut_r2, show s.getReg 2#5 + 4294967280#32 + 8#32 = s.getReg 2#5 + 4294967288#32 by bv_omega,
        read_write_same4]
    have hcs' : ∀ r : Reg, calleeSaved r → r ≠ 2#5 → r ≠ 8#5 → S.getReg r = s.getReg r := fun r hr h2 h8 => by
      rcases calleeSaved_cases r hr with h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst h <;>
        first | exact absurd rfl h2 | exact absurd rfl h8 | assumption
    obtain ⟨m, t, hrun, hpct, hpost, hcst, hfrt⟩ := merkle_from9 A s S (s.getReg 10#5) (s.getReg 12#5) hpc
      (by simp only [ROM_END]; omega) hAbr (codeAt_of_rom hcode (by rw [show Code.merkle_step.length = 72 from rfl]; simp only [ROM_END]; omega) srom)
      (codeAt_of_rom hbl hAbr srom) cut_pc cut_r2 cut_r10 cut_r11 cut_r12 hra' hs0' hcs' hmem hra hsp
      (by simp only [ROM_END]; omega) ha4 hspa (by simp only [RAM_END]; omega) ha4 hspa
      (by simp only [RAM_END]; omega) hs4 hs1 (by simp only [RAM_END]; omega) (by omega)
    exact ⟨m, t, hrun, hpct, by simp only [merklePost, hr, ne_eq, not_true_eq_false, ite_false]; exact hpost,
      hcst, hfrt⟩
  · rv_steps 4 with hentry
    apply run_of_step
    rv_step_simp with hentry
    rv_steps 3 with hentry
    rv_cut
    have srom : ∀ b : Word, b.toNat < ROM_END → S.mem b = s.mem b := fun b hb => by
      simp only [ROM_END] at hb
      rw [cut_mem]
      repeat rw [write_outside (h := Or.inl (by bv_omega)) (ha := by bv_omega)]
    have hmem : ∀ a : Word, a.toNat + 8 < (s.getReg 2#5).toNat ∨ (s.getReg 2#5).toNat ≤ a.toNat →
        S.mem a = s.mem a := fun a ha => by
      rw [cut_mem]
      repeat rw [write_outside (h := by bv_omega) (ha := by bv_omega)]
    have hra' : read S.mem (S.getReg 2#5 + 12#32) 4 = s.getReg 1#5 := by
      rw [cut_mem, cut_r2, read_write_disjoint (h := by bv_omega) (ha := by bv_omega) (hc := by bv_omega),
        show s.getReg 2#5 + 4294967280#32 + 12#32 = s.getReg 2#5 + 4294967292#32 by bv_omega, read_write_same4]
    have hs0' : read S.mem (S.getReg 2#5 + 8#32) 4 = s.getReg 8#5 := by
      rw [cut_mem, cut_r2, show s.getReg 2#5 + 4294967280#32 + 8#32 = s.getReg 2#5 + 4294967288#32 by bv_omega,
        read_write_same4]
    have hcs' : ∀ r : Reg, calleeSaved r → r ≠ 2#5 → r ≠ 8#5 → S.getReg r = s.getReg r := fun r hr h2 h8 => by
      rcases calleeSaved_cases r hr with h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst h <;>
        first | exact absurd rfl h2 | exact absurd rfl h8 | assumption
    obtain ⟨m, t, hrun, hpct, hpost, hcst, hfrt⟩ := merkle_from9 A s S (s.getReg 12#5) (s.getReg 10#5) hpc
      (by simp only [ROM_END]; omega) hAbr (codeAt_of_rom hcode (by rw [show Code.merkle_step.length = 72 from rfl]; simp only [ROM_END]; omega) srom)
      (codeAt_of_rom hbl hAbr srom) cut_pc cut_r2 cut_r10 cut_r11 cut_r12 hra' hs0' hcs' hmem hra hsp
      (by simp only [ROM_END]; omega) ha4 hspa (by simp only [RAM_END]; omega) hs4 hs1
      (by simp only [RAM_END]; omega) ha4 hspa (by simp only [RAM_END]; omega) (by omega)
    exact ⟨m, t, hrun, hpct, by simp only [merklePost, hr, ne_eq, not_false_eq_true, ite_true]; exact hpost,
      hcst, hfrt⟩

end RV
