import Slop.RV.Ext4Call
import Slop.RV.Coeffs4
import Slop.RV.Ext4Poly.AValues

/-! `ext4_poly` in plain Rust, up to the call of `ext4_horner`: block A (`yy = new(y)` twice into the frame, saved
registers, call arguments) and the `jal`. -/

namespace RV
open _root_.RV.Sym Spec
set_option maxHeartbeats 400000

namespace PolyA
abbrev rSp : Region := ⟨2, -64, 0, 16⟩
abbrev rY : Region := ⟨11, 0, 16, 4⟩
end PolyA
open PolyA

theorem word86 (h : 86 < Code.ext4_poly.length) : Code.ext4_poly[86]'h = 0x81dff0ef#32 := rfl

/-- After block A and the `jal`: at `ext4_horner` (`A - 0x68c`) with its arguments (`out = sp - 44`, the table,
`n = 32`, `x = yy = sp - 60` holding `y` in Montgomery form), the constants `p - 1, p, K` in `s2 … s4`, the saved
registers in the frame `[sp - 64, sp)`, and nothing else changed. -/
theorem poly_part_a (A : Word) (s : State) (hpc : s.pc = A) (hcode : CodeAt s A Code.ext4_poly)
    (hal : A.toNat % 4 = 0) (hrom : A.toNat + 560 ≤ ROM_END) (hA : 0x68c ≤ A.toNat)
    (hsp16 : (s.getReg 2#5).toNat % 16 = 0) (hspl : ROM_END + 192 ≤ (s.getReg 2#5).toNat)
    (hspT : (s.getReg 2#5).toNat ≤ 0x1400190)
    (hy4 : (s.getReg 11#5).toNat % 4 = 0) (hys : (s.getReg 2#5).toNat ≤ (s.getReg 11#5).toNat)
    (hyr : (s.getReg 11#5).toNat + 16 ≤ RAM_END) (hcy : canon4 s.mem (s.getReg 11#5)) :
    ∃ S1, run 87 s = some S1 ∧ S1.pc = A + 4294965620#32 ∧ S1.getReg 1#5 = A + 348#32 ∧
      S1.getReg 2#5 = s.getReg 2#5 + 4294967232#32 ∧ S1.getReg 10#5 = s.getReg 2#5 + 4294967252#32 ∧
      S1.getReg 11#5 = 20971920#32 ∧ S1.getReg 12#5 = 32#32 ∧ S1.getReg 13#5 = s.getReg 2#5 + 4294967236#32 ∧
      S1.getReg 9#5 = s.getReg 10#5 ∧ S1.getReg 18#5 = 2013265920#32 ∧ S1.getReg 19#5 = 2013265921#32 ∧
      S1.getReg 20#5 = 2013265919#32 ∧
      (∀ r : Reg, 22 ≤ r.toNat → r.toNat ≤ 27 → S1.getReg r = s.getReg r) ∧
      (∀ b : Word, b.toNat < ROM_END → S1.mem b = s.mem b) ∧
      (∀ a : Word, a.toNat + 64 < (s.getReg 2#5).toNat ∨ (s.getReg 2#5).toNat ≤ a.toNat → S1.mem a = s.mem a) ∧
      canon4 S1.mem (s.getReg 2#5 + 4294967236#32) ∧
      e4At S1.mem (s.getReg 2#5 + 4294967236#32) = limbsAt s.mem (s.getReg 11#5) ∧
      read S1.mem (s.getReg 2#5 + 4294967292#32) 4 = s.getReg 1#5 ∧
      read S1.mem (s.getReg 2#5 + 4294967288#32) 4 = s.getReg 8#5 ∧
      read S1.mem (s.getReg 2#5 + 4294967284#32) 4 = s.getReg 9#5 ∧
      read S1.mem (s.getReg 2#5 + 4294967280#32) 4 = s.getReg 18#5 ∧
      read S1.mem (s.getReg 2#5 + 4294967276#32) 4 = s.getReg 19#5 ∧
      read S1.mem (s.getReg 2#5 + 4294967272#32) 4 = s.getReg 20#5 ∧
      read S1.mem (s.getReg 2#5 + 4294967268#32) 4 = s.getReg 21#5 := by
  have hlen : Code.ext4_poly.length = 140 := by decide +kernel
  simp only [ROM_END, RAM_END] at *
  obtain ⟨S1, hrun1, hpc1, hrel1, hrom1, hout1, hfr1⟩ := block_from _ PolyA.instrs PolyA.σ s A [rSp, rY]
    [(rSp, rY)] PolyA.dec PolyA.run hpc hal (by simp [hlen, ROM_END]; omega) (codeAt_take hcode 86)
    (by sym_side) (by sym_side) (by decide +kernel)
  rw [List.length_take, hlen, show min 86 140 = 86 from rfl] at hrun1 hpc1
  -- the `jal` to `ext4_horner`
  have hw : read S1.mem S1.pc 4 = 0x81dff0ef#32 := by
    rw [read_congr S1.mem s.mem _ 4 (fun j hj => hrom1 _ (by rw [hpc1]; simp only [ROM_END]; bv_omega)), hpc1]
    exact (hcode 86 (by rw [hlen]; omega)).trans (word86 _)
  have hdec : decode 0x81dff0ef#32 = some (.jal 1#5 4294965276#32) := by decide +kernel
  obtain ⟨S1j, hS1j⟩ : ∃ T, T = (S1.setPC (S1.pc + 4294965276#32)).setReg 1#5 (S1.pc + 4) := ⟨_, rfl⟩
  have hstep : step S1 = some S1j := by
    rw [step_fetch S1 _ (by rw [hpc1]; bv_omega) (by rw [hpc1]; simp only [ROM_END]; bv_omega) hw, hdec,
      Option.bind_some, exec_jal S1 _ _ (by rw [hpc1]; bv_omega), hS1j]
  have g : ∀ r : Reg, r ≠ 1#5 → S1j.getReg r = S1.getReg r := fun r hr => by
    rw [hS1j, r_set, jump_r]; simp only [hr, ite_false]
    split
    · next h => subst h; rfl
    · rfl
  have gm : S1j.mem = S1.mem := by rw [hS1j, set_mem, jump_mem]
  -- the block's results
  have ld : ∀ i b (k : Word), b < 32 → i < PolyA.σ.pool.len → nodeAt PolyA.σ.pool i = .load 4 true b k →
      PolyA.σ.pool.val (ctxOf s) i = read s.mem (s.getReg (BitVec.ofNat 5 b) + k) 4 :=
    fun i b k hb hi h => load_val _ _ PolyA.run s i b k true hb hi h
  have l34 := ld 34 11 0#32 (by decide) (by decide +kernel) (by decide +kernel)
  have l35 := ld 35 11 4#32 (by decide) (by decide +kernel) (by decide +kernel)
  have l36 := ld 36 11 8#32 (by decide) (by decide +kernel) (by decide +kernel)
  have l38 := ld 38 11 12#32 (by decide) (by decide +kernel) (by decide +kernel)
  have z : ∀ r : Reg, s.getReg r + 0#32 = s.getReg r := fun r => by simp
  simp only [z] at l34
  simp only [canon4] at hcy
  obtain ⟨b90, b91, b95, b96, m90, m91, m95, m96⟩ := PolyA.values (ctxOf s)
    (by rw [l34]; exact hcy.1) (by rw [l35]; exact hcy.2.1) (by rw [l36]; exact hcy.2.2.1) (by rw [l38]; exact hcy.2.2.2)
  have o := fun k (h : outOK PolyA.σ [rSp, rY] [(rSp, rY)] 2 k = true) => hout1 2 k (by decide) h
  have o90 := o 4294967236#32 (by decide +kernel)
  have o91 := o 4294967240#32 (by decide +kernel)
  have o95 := o 4294967244#32 (by decide +kernel)
  have o96 := o 4294967248#32 (by decide +kernel)
  rw [show outNode PolyA.σ 2 4294967236#32 = 90 by decide +kernel] at o90
  rw [show outNode PolyA.σ 2 4294967240#32 = 91 by decide +kernel] at o91
  rw [show outNode PolyA.σ 2 4294967244#32 = 95 by decide +kernel] at o95
  rw [show outNode PolyA.σ 2 4294967248#32 = 96 by decide +kernel] at o96
  have slot : ∀ (k : Word) (i : Nat), i < 32 → outOK PolyA.σ [rSp, rY] [(rSp, rY)] 2 k = true →
      outNode PolyA.σ 2 k = i → read S1j.mem (s.getReg 2#5 + k) 4 = s.getReg (BitVec.ofNat 5 i) :=
    fun k i hi h hn => by rw [gm]; exact (hout1 2 k (by decide) h).trans (by rw [hn, val_init _ _ PolyA.run s i hi])
  refine ⟨S1j, ?_, by rw [hS1j]; simp only [State.setReg, State.setPC, hpc1]; bv_omega,
    by rw [hS1j, r_set, jump_r, hpc1]; simp only [ite_true]; simp; bv_omega, ?_⟩
  · rw [show 87 = 86 + 1 from rfl, run_add, hrun1, Option.bind_some, run_succ, hstep]; rfl
  refine ⟨(g _ (by decide)).trans (hrel1.reg_addr _ PolyA.run 2#5 2 _ (by decide) (by decide +kernel) (by decide +kernel)),
    (g _ (by decide)).trans (hrel1.reg_addr _ PolyA.run 10#5 2 _ (by decide) (by decide +kernel) (by decide +kernel)),
    (g _ (by decide)).trans (hrel1.reg_cst 11#5 _ (by decide +kernel)),
    (g _ (by decide)).trans (hrel1.reg_cst 12#5 _ (by decide +kernel)),
    (g _ (by decide)).trans (hrel1.reg_addr _ PolyA.run 13#5 2 _ (by decide) (by decide +kernel) (by decide +kernel)),
    (g _ (by decide)).trans (hrel1.reg_var _ PolyA.run 9#5 10 (by decide) (by decide +kernel)),
    (g _ (by decide)).trans (hrel1.reg_cst 18#5 _ (by decide +kernel)),
    (g _ (by decide)).trans (hrel1.reg_cst 19#5 _ (by decide +kernel)),
    (g _ (by decide)).trans (hrel1.reg_cst 20#5 _ (by decide +kernel)), ?_, fun b hb => by rw [gm]; exact hrom1 b hb, ?_, ?_, ?_,
    slot _ 1 (by decide) (by decide +kernel) (by decide +kernel),
    slot _ 8 (by decide) (by decide +kernel) (by decide +kernel),
    slot _ 9 (by decide) (by decide +kernel) (by decide +kernel),
    slot _ 18 (by decide) (by decide +kernel) (by decide +kernel),
    slot _ 19 (by decide) (by decide +kernel) (by decide +kernel),
    slot _ 20 (by decide) (by decide +kernel) (by decide +kernel),
    slot _ 21 (by decide) (by decide +kernel) (by decide +kernel)⟩
  · intro r h1 h2
    have : r = 22#5 ∨ r = 23#5 ∨ r = 24#5 ∨ r = 25#5 ∨ r = 26#5 ∨ r = 27#5 := by bv_omega
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact (g _ (by decide)).trans (hrel1.reg_var _ PolyA.run _ _ (by decide) (by decide +kernel))
  · intro a ha
    rw [gm]
    apply hfr1 [⟨2, -64, 0, 1⟩] (by decide +kernel) (by sym_side) a
    intro R hR
    simp only [List.mem_singleton] at hR
    subst hR
    simp only [Region.Outside]
    omega
  · simp only [canon4, gm, BitVec.add_assoc, BitVec.reduceAdd, o90, o91, o95, o96]
    exact ⟨b90, b91, b95, b96⟩
  · simp only [e4At, e4, gm, BitVec.add_assoc, BitVec.reduceAdd, o90, o91, o95, o96, m90, m91, m95, m96, limbsAt,
      l34, l35, l36, l38]

end RV
