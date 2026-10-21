import Slop.RV.FsCheck.Values
import Slop.RV.Jal
import Slop.RV.Ext4Call

/-! `fs_check(st, v)`, part A: the frame, the challenge `z` (`red` of the 4 words at `st`) at `sp - 56`, and the call
of `ext4_poly(sp - 40, sp - 56)`. -/

namespace RV
open _root_.RV.Sym Spec
set_option maxHeartbeats 400000

namespace FsPartA
abbrev rF : Region := ⟨2, -64, 0, 16⟩
abbrev rSt : Region := ⟨10, 0, 16, 4⟩
end FsPartA
open FsPartA

theorem fs_part_a (A off : Word) (s : State) (codeF : List Word) (hpc : s.pc = A) (hal : A.toNat % 4 = 0)
    (hrom : A.toNat + 4 * 54 ≤ ROM_END) (hcode : CodeAt s A codeF) (hlen : 54 ≤ codeF.length)
    (hb : codeF.take 53 = Code.fs_check.take 53) (j : Word) (hj : codeF[53]? = some j)
    (dj : decode j = some (.jal 1#5 off)) (htgt : (A + BitVec.ofNat 32 (4 * 53) + off).toNat % 4 = 0)
    (hsp16 : (s.getReg 2#5).toNat % 16 = 0) (hspl : ROM_END + 64 ≤ (s.getReg 2#5).toNat)
    (hsph : (s.getReg 2#5).toNat ≤ RAM_END) (hst : argOk (s.getReg 2#5) (s.getReg 10#5)) :
    ∃ S1, run 54 s = some S1 ∧ S1.pc = A + BitVec.ofNat 32 (4 * 53) + off ∧
      S1.getReg 1#5 = A + BitVec.ofNat 32 (4 * 53) + 4 ∧ S1.getReg 2#5 = s.getReg 2#5 + 4294967232#32 ∧
      S1.getReg 10#5 = s.getReg 2#5 + 4294967256#32 ∧ S1.getReg 11#5 = s.getReg 2#5 + 4294967240#32 ∧
      S1.getReg 9#5 = s.getReg 11#5 ∧ S1.getReg 8#5 = s.getReg 2#5 ∧
      S1.getReg 18#5 = 0x78000000#32 ∧ S1.getReg 19#5 = 0x87ffffff#32 ∧
      (∀ r : Reg, 20 ≤ r.toNat → r.toNat ≤ 27 → S1.getReg r = s.getReg r) ∧
      (∀ b : Word, b.toNat < ROM_END → S1.mem b = s.mem b) ∧
      (∀ a : Word, a.toNat + 64 < (s.getReg 2#5).toNat ∨ (s.getReg 2#5).toNat ≤ a.toNat → S1.mem a = s.mem a) ∧
      read S1.mem (s.getReg 2#5 + 4294967240#32) 4 = red (read s.mem (s.getReg 10#5) 4) ∧
      read S1.mem (s.getReg 2#5 + 4294967244#32) 4 = red (read s.mem (s.getReg 10#5 + 4#32) 4) ∧
      read S1.mem (s.getReg 2#5 + 4294967248#32) 4 = red (read s.mem (s.getReg 10#5 + 8#32) 4) ∧
      read S1.mem (s.getReg 2#5 + 4294967252#32) 4 = red (read s.mem (s.getReg 10#5 + 12#32) 4) ∧
      read S1.mem (s.getReg 2#5 + 4294967292#32) 4 = s.getReg 1#5 ∧
      read S1.mem (s.getReg 2#5 + 4294967288#32) 4 = s.getReg 8#5 ∧
      read S1.mem (s.getReg 2#5 + 4294967284#32) 4 = s.getReg 9#5 ∧
      read S1.mem (s.getReg 2#5 + 4294967280#32) 4 = s.getReg 18#5 ∧
      read S1.mem (s.getReg 2#5 + 4294967276#32) 4 = s.getReg 19#5 := by
  obtain ⟨_, e53⟩ := List.getElem?_eq_some_iff.mp hj
  obtain ⟨hst4, hsts, hstr⟩ := hst
  simp only [ROM_END, RAM_END] at *
  have h2n := hspl
  have hlA : (Code.fs_check.take 53).length = 53 := by decide +kernel
  have hc : CodeAt s A (Code.fs_check.take 53) := hb ▸ codeAt_take hcode 53
  obtain ⟨T, hrun, hrel, hromT, hout, hfr⟩ := block_jal _ FsA.instrs FsA.σ s A off [rF, rSt] [(rF, rSt)]
    FsA.dec FsA.run hpc hal (by rw [hlA]; simp only [ROM_END]; omega) hc j (by rw [hlA]; exact (hcode 53 (by omega)).trans e53)
    dj (by rw [hlA]; exact htgt) (by sym_side) (by sym_side) (by decide +kernel)
  rw [hlA] at hrun
  set S1 := (T.setPC (A + BitVec.ofNat 32 (4 * 53) + off)).setReg 1#5 (A + BitVec.ofNat 32 (4 * 53) + 4) with hS1
  have g : ∀ r : Reg, r ≠ 1#5 → S1.getReg r = T.getReg r := fun r hr => by rw [hS1, jal_getReg _ _ _ _ hr]
  have gm : S1.mem = T.mem := by rw [hS1, jal_mem]
  have sp2 : ∀ (k : Word) (i : Nat), outOK FsA.σ [rF, rSt] [(rF, rSt)] 2 k = true → outNode FsA.σ 2 k = i →
      read S1.mem (s.getReg 2#5 + k) 4 = FsA.σ.pool.val (ctxOf s) i := fun k i h hn => by
    rw [gm, ← hn]; exact hout 2 k (by decide) h
  obtain ⟨z0, z1, z2, z3⟩ := fsA_z (ctxOf s)
  have vi : ∀ i (hi : i < 32), FsA.σ.pool.val (ctxOf s) i = s.getReg (BitVec.ofNat 5 i) := fun i hi =>
    val_init _ _ FsA.run s i hi
  refine ⟨S1, hrun, by rw [hS1, jal_pc], by rw [hS1, jal_getReg1], ?_, ?_, ?_, ?_, ?_,
    (g _ (by decide)).trans (hrel.reg_cst 18#5 _ (by decide +kernel)),
    (g _ (by decide)).trans (hrel.reg_cst 19#5 _ (by decide +kernel)), ?_,
    fun b hb => by rw [gm]; exact hromT b (by simp only [ROM_END]; omega), ?_,
    (sp2 _ 54 (by decide +kernel) (by decide +kernel)).trans z0, (sp2 _ 57 (by decide +kernel) (by decide +kernel)).trans z1,
    (sp2 _ 71 (by decide +kernel) (by decide +kernel)).trans z2, (sp2 _ 72 (by decide +kernel) (by decide +kernel)).trans z3,
    (sp2 _ 1 (by decide +kernel) (by decide +kernel)).trans (vi 1 (by decide)),
    (sp2 _ 8 (by decide +kernel) (by decide +kernel)).trans (vi 8 (by decide)),
    (sp2 _ 9 (by decide +kernel) (by decide +kernel)).trans (vi 9 (by decide)),
    (sp2 _ 18 (by decide +kernel) (by decide +kernel)).trans (vi 18 (by decide)),
    (sp2 _ 19 (by decide +kernel) (by decide +kernel)).trans (vi 19 (by decide))⟩
  · rw [g _ (by decide), hrel.reg_addr _ FsA.run 2#5 2 4294967232#32 (by decide) (by decide +kernel) (by decide +kernel)]
  · rw [g _ (by decide), hrel.reg_addr _ FsA.run 10#5 2 4294967256#32 (by decide) (by decide +kernel) (by decide +kernel)]
  · rw [g _ (by decide), hrel.reg_addr _ FsA.run 11#5 2 4294967240#32 (by decide) (by decide +kernel) (by decide +kernel)]
  · rw [g _ (by decide), hrel.reg_var _ FsA.run 9#5 11 (by decide) (by decide +kernel)]
  · rw [g _ (by decide), hrel.reg_addr _ FsA.run 8#5 2 0#32 (by decide) (by decide +kernel) (by decide +kernel)]
    simp
  · intro r h1 h2
    rw [g _ (by rintro rfl; simp at h1)]
    have : r = 20#5 ∨ r = 21#5 ∨ r = 22#5 ∨ r = 23#5 ∨ r = 24#5 ∨ r = 25#5 ∨ r = 26#5 ∨ r = 27#5 := by bv_omega
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact hrel.reg_same _ FsA.run _ (by decide +kernel)
  · intro a ha
    rw [gm]
    apply hfr [⟨2, -64, 0, 1⟩] (by decide +kernel) (by sym_side) a
    intro R hR; simp only [List.mem_singleton] at hR; subst hR
    simp only [Region.Outside]; omega

end RV
