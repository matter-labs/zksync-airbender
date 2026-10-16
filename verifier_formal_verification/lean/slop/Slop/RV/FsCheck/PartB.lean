import Slop.RV.FsCheck.Values
import Slop.RV.Jal
import Slop.RV.Ext4Call
import Slop.RV.CopyRun
import Slop.RV.Stuck

/-! `fs_check(st, v)`, part B, after `ext4_poly` returns: the comparison (block B) and its branch; then either the
epilogue and `ret` (the claim is right), or `zksync_os_finish_error`, whose `csrrw x0, cycle, x0` has no next state
(the claim is wrong). -/

namespace RV
open _root_.RV.Sym Spec
set_option maxHeartbeats 0

namespace FsPartB
abbrev rF : Region := ⟨2, 0, 64, 16⟩
abbrev rV : Region := ⟨9, 0, 16, 4⟩
abbrev rE : Region := ⟨2, -16, 0, 16⟩
end FsPartB
open FsPartB

/-- The four computed limbs (at `out`) are the claimed ones (at `v`), reduced. -/
def limbsMatch (m : Word → BitVec 8) (out v : Word) : Prop :=
  read m out 4 = red (read m v 4) ∧ read m (out + 4#32) 4 = red (read m (v + 4#32) 4) ∧
  read m (out + 8#32) 4 = red (read m (v + 8#32) 4) ∧ read m (out + 12#32) 4 = red (read m (v + 12#32) 4)

theorem fs_part_b (A Aerr : Word) (s S2 : State) (codeF : List Word) (hal : A.toNat % 4 = 0)
    (hrom : A.toNat + 4 * 113 ≤ ROM_END) (hpc : S2.pc = A + BitVec.ofNat 32 (4 * 54))
    (hcode : CodeAt S2 A codeF) (hlen : codeF.length = 113)
    (hb : (codeF.drop 54).take 58 = (Code.fs_check.drop 54).take 58)
    (j : Word) (hj : codeF[112]? = some j)
    (dj : decode j = some (.jal 1#5 (Aerr - (A + BitVec.ofNat 32 (4 * 112)))))
    (herr : CodeAt S2 Aerr Code.finish_error) (hAerr : Aerr.toNat % 4 = 0) (hAerrr : Aerr.toNat + 24 ≤ ROM_END)
    (hsp16 : (s.getReg 2#5).toNat % 16 = 0) (hspl : ROM_END + 80 ≤ (s.getReg 2#5).toNat)
    (hsph : (s.getReg 2#5).toNat ≤ RAM_END) (hv : argOk (s.getReg 2#5) (s.getReg 11#5))
    (hra : (s.getReg 1#5).toNat % 4 = 0)
    (h2 : S2.getReg 2#5 = s.getReg 2#5 + 4294967232#32) (h9 : S2.getReg 9#5 = s.getReg 11#5)
    (h18 : S2.getReg 18#5 = 0x78000000#32) (h19 : S2.getReg 19#5 = 0x87ffffff#32)
    (hr : ∀ r : Reg, 20 ≤ r.toNat → r.toNat ≤ 27 → S2.getReg r = s.getReg r)
    (k1 : read S2.mem (s.getReg 2#5 + 4294967292#32) 4 = s.getReg 1#5)
    (k8 : read S2.mem (s.getReg 2#5 + 4294967288#32) 4 = s.getReg 8#5)
    (k9 : read S2.mem (s.getReg 2#5 + 4294967284#32) 4 = s.getReg 9#5)
    (k18 : read S2.mem (s.getReg 2#5 + 4294967280#32) 4 = s.getReg 18#5)
    (k19 : read S2.mem (s.getReg 2#5 + 4294967276#32) 4 = s.getReg 19#5) :
    ∃ m T, run m S2 = some T ∧
      (limbsMatch S2.mem (s.getReg 2#5 + 4294967256#32) (s.getReg 11#5) →
        T.pc = s.getReg 1#5 ∧ (∀ i, calleeSaved i → T.getReg i = s.getReg i) ∧
        (∀ a : Word, a.toNat + 64 < (s.getReg 2#5).toNat ∨ (s.getReg 2#5).toNat ≤ a.toNat → T.mem a = S2.mem a)) ∧
      (¬ limbsMatch S2.mem (s.getReg 2#5 + 4294967256#32) (s.getReg 11#5) → AtFinishError T) := by
  obtain ⟨_, e112⟩ := List.getElem?_eq_some_iff.mp hj
  obtain ⟨hv4, hvs, hvr⟩ := hv
  simp only [ROM_END, RAM_END] at *
  have h2n : (S2.getReg 2#5).toNat = (s.getReg 2#5).toNat - 64 := by rw [h2]; bv_omega
  have h9n : (S2.getReg 9#5).toNat = (s.getReg 11#5).toNat := by rw [h9]
  have hc58 : CodeAt S2 (A + BitVec.ofNat 32 (4 * 54)) ((Code.fs_check.drop 54).take 58) :=
    hb ▸ codeAt_take (codeAt_drop hcode 54 (by rw [hlen]; omega)) 58
  have hL58 : ((Code.fs_check.drop 54).take 58).length = 58 := by decide +kernel
  have hL50 : ((Code.fs_check.drop 54).take 50).length = 50 := by decide +kernel
  have hL6 : ((Code.fs_check.drop 105).take 6).length = 6 := by decide +kernel
  have w : ∀ k (hk : k < 58), read S2.mem (A + BitVec.ofNat 32 (4 * (54 + k))) 4 =
      ((Code.fs_check.drop 54).take 58)[k]'(by rw [hL58]; omega) := fun k hk => by
    rw [← hc58 k (by rw [hL58]; omega)]; congr 1; bv_omega
  ------------------------------------------------------------------ block B
  have hcB : CodeAt S2 (A + BitVec.ofNat 32 (4 * 54)) ((Code.fs_check.drop 54).take 50) := by
    have := codeAt_take hc58 50
    rwa [show ((Code.fs_check.drop 54).take 58).take 50 = (Code.fs_check.drop 54).take 50 by decide +kernel] at this
  obtain ⟨S3, hrun3, hpc3, hrel3, hrom3, -, hfr3⟩ := block_from _ FsB.instrs FsB.σ S2 _ [rF, rV] [(rF, rV)]
    FsB.dec FsB.run hpc (by bv_omega) (by rw [hL50]; simp only [ROM_END]; bv_omega) hcB (by sym_side) (by sym_side)
    (by decide +kernel)
  rw [hL50] at hrun3 hpc3
  have hpc3' : S3.pc = A + BitVec.ofNat 32 (4 * (54 + 50)) := by rw [hpc3]; bv_omega
  have s3rom : ∀ b : Word, b.toNat < 4194304 → S3.mem b = S2.mem b := fun b hb => hrom3 b (by simp only [ROM_END]; omega)
  have s3fr : ∀ a : Word, a.toNat + 24 < (s.getReg 2#5).toNat ∨ (s.getReg 2#5).toNat ≤ a.toNat + 20 →
      S3.mem a = S2.mem a := fun a ha => by
    apply hfr3 [⟨2, 40, 44, 1⟩] (by decide +kernel) (by sym_side) a
    intro R hR; simp only [List.mem_singleton] at hR; subst hR
    simp only [Region.Outside, show (BitVec.ofNat 5 2 : Reg) = 2#5 from rfl]; omega
  have hdiff : S3.getReg 10#5 = 0#32 ↔ limbsMatch S2.mem (s.getReg 2#5 + 4294967256#32) (s.getReg 11#5) := by
    rw [(hrel3.2.2.1 10#5).2, show (FsB.σ.reg 10#5).val = 78 by decide +kernel,
      fsB_diff (ctxOf S2) (by show S2.getReg (BitVec.ofNat 5 18) = _; exact h18)
        (by show S2.getReg (BitVec.ofNat 5 19) = _; exact h19)]
    simp only [ctxOf, limbsMatch, show (BitVec.ofNat 5 2 : Reg) = 2#5 from rfl, show (BitVec.ofNat 5 9 : Reg) = 9#5
      from rfl, h2, h9, BitVec.add_assoc, BitVec.reduceAdd]
  ------------------------------------------------------------------ the branch
  have wb : read S3.mem S3.pc 4 = 0x02051063#32 := by
    rw [read_congr S3.mem S2.mem _ 4 (fun j hj => s3rom _ (by rw [hpc3']; bv_omega)), hpc3']
    exact w 50 (by decide)
  have hdb : decode 0x02051063#32 = some (.branch .ne 10#5 0#5 32#32) := by decide +kernel
  by_cases hok : limbsMatch S2.mem (s.getReg 2#5 + 4294967256#32) (s.getReg 11#5)
  · ---------------------------------------------------------------- right: epilogue, `ret`
    have hz := hdiff.mpr hok
    have hst : step S3 = some S3.nextInstr := by
      rw [step_fetch S3 _ (by rw [hpc3']; bv_omega) (by rw [hpc3']; simp only [ROM_END]; bv_omega) wb, hdb,
        Option.bind_some, exec_branch_f _ _ _ _ _ (by simp [Cond.holds, hz, r_zero5])]
    set S4 := S3.nextInstr with hS4
    have hpc4 : S4.pc = A + BitVec.ofNat 32 (4 * 105) := by rw [hS4, next_pc, hpc3']; bv_omega
    have s3sp : S3.getReg 2#5 = s.getReg 2#5 + 4294967232#32 := by
      rw [hrel3.reg_same _ FsB.run _ (by decide +kernel), h2]
    have h4sp : (S4.getReg 2#5).toNat = (s.getReg 2#5).toNat - 64 := by rw [hS4, next_r, s3sp]; bv_omega
    have hcE : CodeAt S4 (A + BitVec.ofNat 32 (4 * 105)) ((Code.fs_check.drop 105).take 6) := by
      intro k hk
      have hk' : k < 6 := by rw [hL6] at hk; exact hk
      rw [hS4, next_mem, read_congr S3.mem S2.mem _ 4 (fun j hj => s3rom _ (by bv_omega)),
        show A + BitVec.ofNat 32 (4 * 105) + BitVec.ofNat 32 (4 * k) = A + BitVec.ofNat 32 (4 * (54 + (51 + k)))
          by bv_omega, w (51 + k) (by omega)]
      interval_cases k <;> rfl
    obtain ⟨S5, hrun5, hpc5, hrel5, hrom5, -, hfr5⟩ := block_from _ FsE.instrs FsE.σ S4 _ [rF] []
      FsE.dec FsE.run hpc4 (by bv_omega) (by rw [hL6]; simp only [ROM_END]; bv_omega) hcE
      (by sym_side)
      (by simp) (by decide +kernel)
    rw [hL6] at hrun5 hpc5
    have hpc5' : S5.pc = A + BitVec.ofNat 32 (4 * (54 + 57)) := by rw [hpc5]; bv_omega
    have s4m : S4.mem = S3.mem := by rw [hS4, next_mem]
    have s5m : S5.mem = S4.mem := by funext a; exact hfr5 [] (by decide +kernel) (by simp) a (by simp)
    -- the saved registers, from the frame (block B wrote only `diff`, at `sp - 24`)
    have ld : ∀ i (k : Word) (v : Word), i < FsE.σ.pool.len → nodeAt FsE.σ.pool i = .load 4 true 2 k →
        44 ≤ k.toNat → k.toNat ≤ 60 → read S2.mem (s.getReg 2#5 + (4294967232#32 + k)) 4 = v →
        FsE.σ.pool.val (ctxOf S4) i = v := fun i k v hi h h1 h2' hv => by
      rw [load_val _ _ FsE.run S4 i 2 k true (by decide) hi h, show (BitVec.ofNat 5 2 : Reg) = 2#5 from rfl, hS4,
        next_r, s3sp, next_mem, BitVec.add_assoc, ← hv]
      exact read_congr _ _ _ _ (fun j hj => s3fr _ (by right; bv_omega))
    have rv : ∀ (r : Reg) (i : Nat), (FsE.σ.reg r).val = i → S5.getReg r = FsE.σ.pool.val (ctxOf S4) i :=
      fun r i h => by rw [(hrel5.2.2.1 r).2, h]
    have r1 : S5.getReg 1#5 = s.getReg 1#5 := by
      rw [rv _ 32 (by decide +kernel)]; exact ld 32 60#32 _ (by decide +kernel) (by decide +kernel) (by decide)
        (by decide) (by simpa using k1)
    have wr : read S5.mem S5.pc 4 = 0x00008067#32 := by
      rw [s5m, s4m, read_congr S3.mem S2.mem _ 4 (fun j hj => s3rom _ (by rw [hpc5']; bv_omega)), hpc5']
      exact w 57 (by decide)
    have hret : step S5 = some ((S5.setPC (S5.getReg 1#5)).setReg 0#5 (S5.pc + 4)) := by
      rw [step_fetch S5 _ (by rw [hpc5']; bv_omega) (by rw [hpc5']; simp only [ROM_END]; bv_omega) wr,
        show decode 0x00008067#32 = some (.jalr 0#5 1#5 0#32) from rfl, Option.bind_some,
        exec_jalr0 S5 _ _ (by rw [r1]; exact hra)]
    refine ⟨50 + 1 + 6 + 1, (S5.setPC (S5.getReg 1#5)).setReg 0#5 (S5.pc + 4), ?_, fun _ => ⟨?_, ?_, ?_⟩,
      fun h => absurd hok h⟩
    · have o1 : run 1 S3 = some S4 := by rw [run_succ, hst]; rfl
      have o2 : run 1 S5 = some ((S5.setPC (S5.getReg 1#5)).setReg 0#5 (S5.pc + 4)) := by rw [run_succ, hret]; rfl
      exact run_trans (run_trans (run_trans hrun3 o1) hrun5) o2
    · simp only [set_pc, jump_pc]; exact r1
    · intro i hi
      have e : ((S5.setPC (S5.getReg 1#5)).setReg 0#5 (S5.pc + 4)).getReg i = S5.getReg i := by
        rw [r_set, jump_r]; split
        · next h => subst h; rfl
        · split
          · next h => exact absurd h (by rcases calleeSaved_cases i hi with h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst h <;> decide)
          · rfl
      rw [e]
      rcases calleeSaved_cases i hi with h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst h
      · rw [hrel5.reg_addr _ FsE.run 2#5 2 64#32 (by decide) (by decide +kernel) (by decide +kernel),
          show (BitVec.ofNat 5 2 : Reg) = 2#5 from rfl, hS4, next_r, s3sp]; bv_omega
      · rw [rv _ 33 (by decide +kernel)]; exact ld 33 56#32 _ (by decide +kernel) (by decide +kernel) (by decide)
          (by decide) (by simpa using k8)
      · rw [rv _ 34 (by decide +kernel)]; exact ld 34 52#32 _ (by decide +kernel) (by decide +kernel) (by decide)
          (by decide) (by simpa using k9)
      · rw [rv _ 35 (by decide +kernel)]; exact ld 35 48#32 _ (by decide +kernel) (by decide +kernel) (by decide)
          (by decide) (by simpa using k18)
      · rw [rv _ 36 (by decide +kernel)]; exact ld 36 44#32 _ (by decide +kernel) (by decide +kernel) (by decide)
          (by decide) (by simpa using k19)
      all_goals
        rw [hrel5.reg_same _ FsE.run _ (by decide +kernel), hS4, next_r, hrel3.reg_same _ FsB.run _ (by decide +kernel)]
        exact hr _ (by decide) (by decide)
    · intro a ha
      simp only [set_mem, jump_mem]
      rw [s5m, s4m]; exact s3fr a (by omega)
  · ---------------------------------------------------------------- wrong: `zksync_os_finish_error`
    have hnz : S3.getReg 10#5 ≠ 0#32 := fun h => hok (hdiff.mp h)
    have hst : step S3 = some (S3.setPC (S3.pc + 32#32)) := by
      rw [step_fetch S3 _ (by rw [hpc3']; bv_omega) (by rw [hpc3']; simp only [ROM_END]; bv_omega) wb, hdb,
        Option.bind_some, exec_branch_t _ _ _ _ _ (by simp [Cond.holds, hnz, r_zero5]) (by rw [hpc3']; bv_omega)]
    set S4 := S3.setPC (S3.pc + 32#32) with hS4
    have hpc4 : S4.pc = A + BitVec.ofNat 32 (4 * 112) := by rw [hS4, jump_pc, hpc3']; bv_omega
    have wj : read S4.mem S4.pc 4 = j := by
      rw [hS4, jump_mem, read_congr S3.mem S2.mem _ 4 (fun j hj => s3rom _ (by rw [← hS4, hpc4]; bv_omega)),
        ← hS4, hpc4]
      exact (hcode 112 (by omega)).trans e112
    have hoff : S4.pc + (Aerr - (A + BitVec.ofNat 32 (4 * 112))) = Aerr := by rw [hpc4]; bv_omega
    have hjs : step S4 = some ((S4.setPC Aerr).setReg 1#5 (S4.pc + 4)) := by
      rw [step_fetch S4 _ (by rw [hpc4]; bv_omega) (by rw [hpc4]; simp only [ROM_END]; bv_omega) wj, dj,
        Option.bind_some, exec_jal S4 _ _ (by rw [hoff]; exact hAerr), hoff]
    set S5 := (S4.setPC Aerr).setReg 1#5 (S4.pc + 4) with hS5
    have s5sp : S5.getReg 2#5 = s.getReg 2#5 + 4294967232#32 := by
      rw [hS5, jal_getReg _ _ _ _ (by decide), hS4, jump_r, hrel3.reg_same _ FsB.run _ (by decide +kernel), h2]
    have s5rom : ∀ b : Word, b.toNat < 4194304 → S5.mem b = S2.mem b := fun b hb => by
      rw [hS5, jal_mem, hS4, jump_mem]; exact s3rom b hb
    have hLe4 : (Code.finish_error.take 4).length = 4 := by decide +kernel
    have hLe : Code.finish_error.length = 6 := by decide +kernel
    have herr5 : CodeAt S5 Aerr Code.finish_error :=
      codeAt_of_rom herr (by rw [hLe]; simp only [ROM_END]; omega) s5rom
    have s5spn : (S5.getReg 2#5).toNat = (s.getReg 2#5).toNat - 64 := by rw [s5sp]; bv_omega
    obtain ⟨S6, hrun6, hpc6, -, hrom6, -, -⟩ := block_from _ FinErr.instrs FinErr.σ S5 Aerr [rE] []
      FinErr.dec FinErr.run (by rw [hS5, jal_pc]) hAerr (by rw [hLe4]; simp only [ROM_END]; omega)
      (codeAt_take herr5 4) (by sym_side) (by simp) (by decide +kernel)
    rw [hLe4] at hrun6 hpc6
    have wu : read S6.mem S6.pc 4 = 0xc0001073#32 := by
      rw [read_congr S6.mem S5.mem _ 4 (fun j hj => hrom6 _ (by rw [hpc6]; simp only [ROM_END]; bv_omega)), hpc6]
      exact herr5 4 (by rw [hLe]; decide)
    refine ⟨50 + 1 + 1 + 4, S6, ?_, fun h => absurd h hok, fun _ => ?_⟩
    · have o1 : run 1 S3 = some S4 := by rw [run_succ, hst]; rfl
      have o2 : run 1 S4 = some S5 := by rw [run_succ, hjs]; rfl
      exact run_trans (run_trans (run_trans hrun3 o1) o2) hrun6
    · exact ⟨by rw [hpc6]; bv_omega, by rw [hpc6]; simp only [ROM_END]; bv_omega, wu⟩

end RV
