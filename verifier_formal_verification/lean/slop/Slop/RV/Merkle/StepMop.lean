import Slop.RV.Merkle.Step
import Slop.RV.Merkle.BlockMop
import Slop.RV.BlakeDeleg.Impl

/-! `merkle_step` of the delegation build: as `Merkle/Step`, with the delegation's evaluator (block at `+128`,
counter at `+192`, 128-aligned) and `blake2s_compress` by the round-function delegation. -/

namespace RV
open Spec
set_option maxHeartbeats 400000

/-- From word 9 (the halves' pointers `L`, `R` in `a1`, `a2`): the block, the tail call, the return to `s`'s `ra`
with the hash of the halves at `a0`. -/
theorem merkle_from9_mop (A : Word) (s S : State) (L R : Word)
    (hal : A.toNat % 4 = 0) (hrom : A.toNat + 4 * 72 ≤ ROM_END)
    (hAbr : (A + 284#32 + 0xFFFFF7D8#32).toNat + 4 * Code.blake2s_compress_mop.length ≤ ROM_END)
    (hcode : CodeAt S A Code.merkle_step_mop) (hbl : CodeAt S (A + 284#32 + 0xFFFFF7D8#32) Code.blake2s_compress_mop)
    (hpc : S.pc = A + 36#32) (h2 : S.getReg 2#5 = s.getReg 2#5 + 4294967280#32) (h10 : S.getReg 10#5 = s.getReg 10#5)
    (h11 : S.getReg 11#5 = L) (h12 : S.getReg 12#5 = R)
    (hra : read S.mem (S.getReg 2#5 + 12#32) 4 = s.getReg 1#5) (hs0 : read S.mem (S.getReg 2#5 + 8#32) 4 = s.getReg 8#5)
    (hcs : ∀ r : Reg, calleeSaved r → r ≠ 2#5 → r ≠ 8#5 → S.getReg r = s.getReg r)
    (hmem : ∀ a : Word, a.toNat + 8 < (s.getReg 2#5).toNat ∨ (s.getReg 2#5).toNat ≤ a.toNat → S.mem a = s.mem a)
    (hra4 : (s.getReg 1#5).toNat % 4 = 0) (hsp : (s.getReg 2#5).toNat % 16 = 0)
    (hsp1 : ROM_END + 16 ≤ (s.getReg 2#5).toNat)
    (ha4 : (s.getReg 10#5).toNat % 128 = 0) (hspa : (s.getReg 2#5).toNat ≤ (s.getReg 10#5).toNat)
    (hR : (s.getReg 10#5).toNat + 196 ≤ RAM_END)
    (hL4 : L.toNat % 4 = 0) (hL1 : (s.getReg 2#5).toNat ≤ L.toNat) (hL2 : L.toNat + 32 ≤ RAM_END)
    (hR4 : R.toNat % 4 = 0) (hR1 : (s.getReg 2#5).toNat ≤ R.toNat) (hR2 : R.toNat + 32 ≤ RAM_END)
    (hRd : R.toNat + 32 ≤ (s.getReg 10#5).toNat + 128 ∨ (s.getReg 10#5).toNat + 160 ≤ R.toNat) :
    ∃ m t, run m S = some t ∧ t.pc = s.getReg 1#5 ∧
      readWords t.mem (s.getReg 10#5) 8 = hash2 (readWords s.mem L 8) (readWords s.mem R 8) ∧
      (∀ i, calleeSaved i → t.getReg i = s.getReg i) ∧
      (∀ a : Word, a.toNat + 16 < (s.getReg 2#5).toNat ∨ (s.getReg 2#5).toNat ≤ a.toNat →
        a.toNat < (s.getReg 10#5).toNat ∨ (s.getReg 10#5).toNat + 196 ≤ a.toNat → t.mem a = s.mem a) := by
  simp only [ROM_END, RAM_END] at *
  have hspn : (S.getReg 2#5).toNat = (s.getReg 2#5).toNat - 16 := by rw [h2]; bv_omega
  obtain ⟨S', hrun, hpc', r10, r11, r12, r1, r8, r2, rcs, hiv, hblk, hct, hfr, hromB⟩ :=
    merkle_block_mop S A hal (by simp only [ROM_END]; rw [show Code.merkle_step_mop.length = 72 from rfl]; omega) hcode hpc
      (by omega) (by simp only [ROM_END]; omega) (by rw [h10]; omega) (by rw [h10]; omega)
      (by rw [h10]; simp only [RAM_END]; omega) (by rw [h11]; exact hL4) (by rw [h11]; simp only [ROM_END]; omega)
      (by rw [h11]; simp only [RAM_END]; omega) (by rw [h12]; exact hR4) (by rw [h12]; simp only [ROM_END]; omega)
      (by rw [h12]; simp only [RAM_END]; omega) (by rw [h10, h12]; omega)
  -- the tail call `jal x0, blake2s_compress`
  set Ab := A + 284#32 + 0xFFFFF7D8#32 with hAb
  have hfetch : read S'.mem S'.pc 4 = 0xfd8ff06f#32 := by
    rw [hpc', read_congr S'.mem S.mem _ 4 (fun j hj => hromB _ (by simp only [ROM_END]; bv_omega))]
    have hw : ∀ h : 71 < Code.merkle_step_mop.length, Code.merkle_step_mop[71]'h = 0xfd8ff06f#32 := by decide +kernel
    exact (hcode 71 (by rw [show Code.merkle_step_mop.length = 72 from rfl]; omega)).trans (hw _)
  have hstep : step S' = some ((S'.setPC Ab).setReg 0#5 (S'.pc + 4)) := by
    rw [step_fetch S' _ (by rw [hpc']; bv_omega) (by rw [hpc']; simp only [ROM_END]; bv_omega) hfetch,
      show decode 0xfd8ff06f#32 = some (.jal 0#5 0xFFFFF7D8#32) by decide +kernel, Option.bind_some,
      exec_jal _ _ _ (by rw [hpc']; simp only [hAb] at hAbr ⊢; bv_omega), hpc']
  obtain ⟨X, hX⟩ : ∃ X, X = (S'.setPC Ab).setReg 0#5 (S'.pc + 4) := ⟨_, rfl⟩
  rw [← hX] at hstep
  have xr : ∀ r : Reg, X.getReg r = S'.getReg r := fun r => by rw [hX, setReg0_getReg, setPC_getReg']
  have xm : X.mem = S'.mem := by rw [hX, setPC_setReg_mem]
  have xsp : X.getReg 2#5 = s.getReg 2#5 := by rw [xr, r2, h2]; bv_omega
  have xrom : ∀ b : Word, b.toNat < ROM_END → X.mem b = S.mem b := fun b hb => by rw [xm, hromB b hb]
  have xpc : X.pc = Ab := by rw [hX]; rfl
  obtain ⟨n, U, hrunU, hpcU, hpost, hcsU, hmemU⟩ := blake2s_compress_mop_impl Ab X xpc (by simp)
    ⟨by rw [xpc]; exact codeAt_of_rom hbl hAbr xrom,
      by rw [xpc]; simp only [hAb]; bv_omega,
      by rw [xpc]; simp only [ROM_END]; omega,
      by show (X.getReg 1#5).toNat % 4 = 0; rw [xr, r1, hra]; exact hra4,
      by show (X.getReg 2#5).toNat % 16 = 0; rw [xsp]; exact hsp,
      by show ROM_END + 16 ≤ (X.getReg 2#5).toNat; rw [xsp]; simp only [ROM_END]; omega,
      by show (X.getReg 2#5).toNat ≤ RAM_END; rw [xsp]; simp only [RAM_END]; omega⟩
    (by simp only [blakeDPre, xsp, xr, r10, r12, h10, RAM_END]; exact ⟨ha4, hspa, hR, Or.inr trivial⟩)
  replace hcsU : ∀ i, calleeSaved i → U.getReg i = X.getReg i := hcsU
  replace hmemU : ∀ a : Word, a.toNat + 16 < (X.getReg 2#5).toNat ∨ (X.getReg 2#5).toNat ≤ a.toNat →
      a.toNat < (X.getReg 10#5).toNat ∨ (X.getReg 10#5).toNat + 196 ≤ a.toNat → U.mem a = X.mem a := hmemU
  simp only [blakeDPost, xr, r10, r11, r12, h10] at hpost
  -- the halves, read where `merkle_check` put them: untouched by the prologue's two stack words
  have hhalf : ∀ P : Word, (s.getReg 2#5).toNat ≤ P.toNat → P.toNat + 32 ≤ 1073741824 →
      wordsAt S.mem P 8 = readWords s.mem P 8 := fun P h1 h2' => by
    apply Vector.ext; intro i hi
    simp only [wordsAt, readWords, Vector.getElem_ofFn]
    exact read_congr _ _ _ _ (fun j hj => hmem _ (by right; bv_omega))
  refine ⟨_, U, run_trans (run_trans hrun (show run 1 S' = some X by rw [run_succ, hstep]; rfl)) hrunU, ?_, ?_, fun i hi => ?_,
    fun a ha hb => ?_⟩
  · rw [hpcU]; show X.getReg 1#5 = _; rw [xr, r1, hra]
  · show readWords U.mem (s.getReg 10#5) 8 = _
    rw [hpost.1, xm, ← h10, show readWords S'.mem (S.getReg 10#5) 8 = _ from hiv,
      show readWords S'.mem (S.getReg 10#5 + 128#32) 16 = _ from hblk, hct, h11, h12, hhalf L hL1 hL2, hhalf R hR1 hR2]
    rfl
  · rw [hcsU i hi, xr]
    by_cases i2 : i = 2#5
    · subst i2; rw [r2, h2]; bv_omega
    by_cases i8 : i = 8#5
    · subst i8; rw [r8, hs0]
    rw [rcs i hi i2 i8, hcs i hi i2 i8]
  · rw [hmemU a (by rw [xsp]; exact ha) (by rw [xr, r10, h10]; exact hb), xm,
      hfr a (by rw [h10]; exact hb), hmem a (by omega)]

theorem merkle_step_mop_impl (A : Word)
    (hAbr : (A + 284#32 + 0xFFFFF7D8#32).toNat + 4 * Code.blake2s_compress_mop.length ≤ ROM_END) :
    ImplementsAtW A Code.merkle_step_mop [(A + 284#32 + 0xFFFFF7D8#32, Code.blake2s_compress_mop)] 16 (merklePre 128 196) 196
      merklePost := by
  intro s hentry hcal ⟨hcode, hal, hrom, hra, hsp, hlo, hhi⟩ ⟨ha4, hspa, hR, hs4, hs1, hs2, hsd⟩
  rw [hentry] at hcode hal hrom
  replace hra : (s.getReg 1#5).toNat % 4 = 0 := hra
  replace hsp : (s.getReg 2#5).toNat % 16 = 0 := hsp
  replace hlo : ROM_END + 16 ≤ (s.getReg 2#5).toNat := hlo
  replace hhi : (s.getReg 2#5).toNat ≤ RAM_END := hhi
  have hL : Code.merkle_step_mop.length = 72 := rfl
  simp only [ROM_END, RAM_END] at hR hs2 hlo hhi
  obtain ⟨m1, S, hrun, hpc, h2, h10, h11, h12, hra', hs0', hcs', hmem, srom⟩ := merkle_side Code.merkle_step_mop
    (by decide +kernel) (by rw [hL]; omega) s A hentry hal hrom hcode (by simp only [ROM_END]; omega)
    (by simp only [RAM_END]; omega) (by omega)
  have hcS := codeAt_of_rom hcode hrom srom
  have hbS := codeAt_of_rom (hcal _ List.mem_cons_self) hAbr srom
  have hrom9 : A.toNat + 4 * 72 ≤ ROM_END := by rw [← hL]; exact hrom
  by_cases hr : s.getReg 11#5 = 0
  · simp only [hr, ↓reduceIte] at h11 h12
    obtain ⟨m, t, hrun', hpct, hpost, hcst, hfrt⟩ := merkle_from9_mop A s S (s.getReg 10#5) (s.getReg 12#5) hal
      hrom9 hAbr hcS hbS hpc h2 h10 h11 h12 hra' hs0' hcs' hmem hra hsp (by simp only [ROM_END]; omega) ha4 hspa
      (by simp only [RAM_END]; omega) (by omega) hspa (by simp only [RAM_END]; omega) hs4 hs1
      (by simp only [RAM_END]; omega) (by omega)
    exact ⟨m1 + m, t, run_trans hrun hrun', hpct, by
      simp only [merklePost, hr, ne_eq, not_true_eq_false, ite_false]; exact hpost, hcst, hfrt⟩
  · simp only [hr, ↓reduceIte] at h11 h12
    obtain ⟨m, t, hrun', hpct, hpost, hcst, hfrt⟩ := merkle_from9_mop A s S (s.getReg 12#5) (s.getReg 10#5) hal
      hrom9 hAbr hcS hbS hpc h2 h10 h11 h12 hra' hs0' hcs' hmem hra hsp (by simp only [ROM_END]; omega) ha4 hspa
      (by simp only [RAM_END]; omega) hs4 hs1 (by simp only [RAM_END]; omega) (by omega) hspa
      (by simp only [RAM_END]; omega) (by omega)
    exact ⟨m1 + m, t, run_trans hrun hrun', hpct, by
      simp only [merklePost, hr, ne_eq, not_false_eq_true, ite_true]; exact hpost, hcst, hfrt⟩

end RV
