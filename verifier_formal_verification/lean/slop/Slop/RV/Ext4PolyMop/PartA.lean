import Slop.RV.Ext4Call
import Slop.RV.Coeffs4
import Slop.RV.Ext4PolyMop.Block

/-! `ext4_poly` with the field opcodes, up to the call of `ext4_horner`: block A (`yy = new(y)` twice into the
frame, saved registers, call arguments) and the `jal`. -/

namespace RV
open _root_.RV.Sym Spec
set_option maxHeartbeats 400000

namespace PolyMA
abbrev rSp : Region := ⟨2, -48, 0, 16⟩
abbrev rY : Region := ⟨11, 0, 16, 4⟩
end PolyMA
open PolyMA

theorem word29 (h : 29 < Code.ext4_poly_mop.length) : Code.ext4_poly_mop[29]'h = 0xe21ff0ef#32 := rfl

/-- After block A and the `jal`: at `ext4_horner` (`A - 0x16c`) with its arguments (`out = sp - 28`, the table,
`n = 32`, `x = yy = sp - 44` holding `y` in Montgomery form), the saved registers in the frame `[sp - 48, sp)`,
and nothing else changed. -/
theorem poly_mop_part_a (A : Word) (s : State) (hpc : s.pc = A) (hcode : CodeAt s A Code.ext4_poly_mop)
    (hal : A.toNat % 4 = 0) (hrom : A.toNat + 192 ≤ ROM_END) (hA : 0x16c ≤ A.toNat)
    (hsp16 : (s.getReg 2#5).toNat % 16 = 0) (hspl : ROM_END + 112 ≤ (s.getReg 2#5).toNat)
    (hspT : (s.getReg 2#5).toNat ≤ 0x1400190)
    (hy4 : (s.getReg 11#5).toNat % 4 = 0) (hys : (s.getReg 2#5).toNat ≤ (s.getReg 11#5).toNat)
    (hyr : (s.getReg 11#5).toNat + 16 ≤ RAM_END) :
    ∃ S1, run 30 s = some S1 ∧ S1.pc = A + 4294966932#32 ∧ S1.getReg 1#5 = A + 120#32 ∧
      S1.getReg 2#5 = s.getReg 2#5 + 4294967248#32 ∧ S1.getReg 10#5 = s.getReg 2#5 + 4294967268#32 ∧
      S1.getReg 11#5 = 20971920#32 ∧ S1.getReg 12#5 = 32#32 ∧ S1.getReg 13#5 = s.getReg 2#5 + 4294967252#32 ∧
      S1.getReg 9#5 = s.getReg 10#5 ∧
      (∀ r : Reg, 18 ≤ r.toNat → r.toNat ≤ 27 → S1.getReg r = s.getReg r) ∧
      (∀ b : Word, b.toNat < ROM_END → S1.mem b = s.mem b) ∧
      (∀ a : Word, a.toNat + 48 < (s.getReg 2#5).toNat ∨ (s.getReg 2#5).toNat ≤ a.toNat → S1.mem a = s.mem a) ∧
      canon4 S1.mem (s.getReg 2#5 + 4294967252#32) ∧
      e4At S1.mem (s.getReg 2#5 + 4294967252#32) = limbsAt s.mem (s.getReg 11#5) ∧
      read S1.mem (s.getReg 2#5 + 4294967292#32) 4 = s.getReg 1#5 ∧
      read S1.mem (s.getReg 2#5 + 4294967288#32) 4 = s.getReg 8#5 ∧
      read S1.mem (s.getReg 2#5 + 4294967284#32) 4 = s.getReg 9#5 := by
  have hlen : Code.ext4_poly_mop.length = 48 := by decide +kernel
  simp only [ROM_END, RAM_END] at *
  obtain ⟨S1, hrun1, hpc1, hrel1, hrom1, hout1, hfr1⟩ := block_from _ PolyMA.instrs PolyMA.σ s A [rSp, rY]
    [(rSp, rY)] PolyMA.dec PolyMA.run hpc hal (by simp [hlen, ROM_END]; omega) (codeAt_take hcode 29)
    (by sym_side) (by sym_side) (by decide +kernel)
  rw [List.length_take, hlen, show min 29 48 = 29 from rfl] at hrun1 hpc1
  -- the `jal` to `ext4_horner`
  have hw : read S1.mem S1.pc 4 = 0xe21ff0ef#32 := by
    rw [read_congr S1.mem s.mem _ 4 (fun j hj => hrom1 _ (by rw [hpc1]; simp only [ROM_END]; bv_omega)), hpc1]
    exact (hcode 29 (by rw [hlen]; omega)).trans (word29 _)
  have hdec : decode 0xe21ff0ef#32 = some (.jal 1#5 4294966816#32) := by decide +kernel
  obtain ⟨S1j, hS1j⟩ : ∃ T, T = (S1.setPC (S1.pc + 4294966816#32)).setReg 1#5 (S1.pc + 4) := ⟨_, rfl⟩
  have hstep : step S1 = some S1j := by
    rw [step_fetch S1 _ (by rw [hpc1]; bv_omega) (by rw [hpc1]; simp only [ROM_END]; bv_omega) hw, hdec,
      Option.bind_some, exec_jal S1 _ _ (by rw [hpc1]; bv_omega), hS1j]
  have g : ∀ r : Reg, r ≠ 1#5 → S1j.getReg r = S1.getReg r := fun r hr => by
    rw [hS1j, r_set, jump_r]; simp only [hr, ite_false]
    split
    · next h => subst h; rfl
    · rfl
  have gm : S1j.mem = S1.mem := by rw [hS1j, set_mem, jump_mem]
  -- the block's results: `yy_k = mop.mul(y_k, R²)`
  have yy : ∀ (k : Word) (i j : Nat) (kk : Word), outOK PolyMA.σ [rSp, rY] [(rSp, rY)] 2 k = true →
      outNode PolyMA.σ 2 k = i → nodeAt PolyMA.σ.pool i = .mop .mul j 36 0 →
      nodeAt PolyMA.σ.pool j = .load 4 true 11 kk → j < PolyMA.σ.pool.len → i < PolyMA.σ.pool.len →
      read S1j.mem (s.getReg 2#5 + k) 4 = mopVal .mul (read s.mem (s.getReg 11#5 + kk) 4) 0x45dddde3#32 0#32 :=
    fun k i j kk h hn hi hj hjl hil => by
      rw [gm, hout1 2 k (by decide) h, hn,
        (nodeAt_spec (ctxOf s) _ PolyMA.wf i hil).2, hi, ← load_val _ _ PolyMA.run s j 11 kk true (by decide) hjl hj]
      simp only [Node.eval]
      rw [(nodeAt_spec (ctxOf s) _ PolyMA.wf 36 (by decide +kernel)).2,
        (nodeAt_spec (ctxOf s) _ PolyMA.wf 0 (by decide +kernel)).2]
      rfl
  have y0 := yy 4294967252#32 37 34 0#32 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have y1 := yy 4294967256#32 39 38 4#32 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have y2 := yy 4294967260#32 41 40 8#32 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have y3 := yy 4294967264#32 43 42 12#32 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [show s.getReg 11#5 + 0#32 = s.getReg 11#5 by simp] at y0
  have slot : ∀ (k : Word) (i : Nat), i < 32 → outOK PolyMA.σ [rSp, rY] [(rSp, rY)] 2 k = true →
      outNode PolyMA.σ 2 k = i → read S1j.mem (s.getReg 2#5 + k) 4 = s.getReg (BitVec.ofNat 5 i) :=
    fun k i hi h hn => by rw [gm]; exact (hout1 2 k (by decide) h).trans (by rw [hn, val_init _ _ PolyMA.run s i hi])
  refine ⟨S1j, ?_, by rw [hS1j]; simp only [State.setReg, State.setPC, hpc1]; bv_omega,
    by rw [hS1j, r_set, jump_r, hpc1]; simp only [ite_true]; simp; bv_omega, ?_⟩
  · rw [show 30 = 29 + 1 from rfl, run_add, hrun1, Option.bind_some, run_succ, hstep]; rfl
  refine ⟨(g _ (by decide)).trans (hrel1.reg_addr _ PolyMA.run 2#5 2 _ (by decide) (by decide +kernel) (by decide +kernel)),
    (g _ (by decide)).trans (hrel1.reg_addr _ PolyMA.run 10#5 2 _ (by decide) (by decide +kernel) (by decide +kernel)),
    (g _ (by decide)).trans (hrel1.reg_cst 11#5 _ (by decide +kernel)),
    (g _ (by decide)).trans (hrel1.reg_cst 12#5 _ (by decide +kernel)),
    (g _ (by decide)).trans (hrel1.reg_addr _ PolyMA.run 13#5 2 _ (by decide) (by decide +kernel) (by decide +kernel)),
    (g _ (by decide)).trans (hrel1.reg_var _ PolyMA.run 9#5 10 (by decide) (by decide +kernel)),
    ?_, fun b hb => by rw [gm]; exact hrom1 b hb, ?_, ?_, ?_,
    slot _ 1 (by decide) (by decide +kernel) (by decide +kernel),
    slot _ 8 (by decide) (by decide +kernel) (by decide +kernel),
    slot _ 9 (by decide) (by decide +kernel) (by decide +kernel)⟩
  · intro r h1 h2
    exact (g _ (by bv_omega)).trans (hrel1.reg_same _ PolyMA.run _ (by
      have : r = 18#5 ∨ r = 19#5 ∨ r = 20#5 ∨ r = 21#5 ∨ r = 22#5 ∨ r = 23#5 ∨ r = 24#5 ∨ r = 25#5 ∨ r = 26#5 ∨
        r = 27#5 := by bv_omega
      rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel))
  · intro a ha
    rw [gm]
    apply hfr1 [⟨2, -48, 0, 1⟩] (by decide +kernel) (by sym_side) a
    intro R hR
    simp only [List.mem_singleton] at hR
    subst hR
    simp only [Region.Outside]
    omega
  · simp only [canon4, BitVec.add_assoc, BitVec.reduceAdd, y0, y1, y2, y3]
    exact ⟨mopVal_lt _ _ _ _ nofun, mopVal_lt _ _ _ _ nofun, mopVal_lt _ _ _ _ nofun, mopVal_lt _ _ _ _ nofun⟩
  · simp only [e4At, e4, BitVec.add_assoc, BitVec.reduceAdd, y0, y1, y2, y3, mont_new, limbsAt]

end RV
