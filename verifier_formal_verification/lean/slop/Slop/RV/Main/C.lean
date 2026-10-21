import Slop.RV.Main.B
import Slop.RV.Finish
import Slop.RV.FinishExt

/-! `main`, last part (both images): the 8 output words to `zksync_os_finish_success`, which ends at its final
self-jump with the outputs in `x10 … x25`. From `main + 0x148`. -/

namespace RV
open _root_.RV.Sym Spec
set_option maxHeartbeats 400000

namespace MainC
abbrev rF : Region := ⟨2, 0, 112, 16⟩
abbrev rBl : Region := ⟨19, 0, 8, 4⟩
end MainC
open MainC

theorem main_c (U : State) (codeM : List Word) (Af : Word) (c p e0 e1 e2 e3 d0 d1 : Word)
    (hAf : Af.toNat % 4 = 0) (hAfr : Af.toNat + 0x78 + 0x84 ≤ 4194304)
    (hpc : U.pc = 0x180#32) (h2 : U.getReg 2#5 = 0x13fff80#32) (h9 : U.getReg 9#5 = c) (h18 : U.getReg 18#5 = p)
    (h19 : U.getReg 19#5 = 0x1401000#32)
    (he0 : read U.mem 0x13fff88#32 4 = e0) (he1 : read U.mem 0x13fff8c#32 4 = e1)
    (he2 : read U.mem 0x13fff90#32 4 = e2) (he3 : read U.mem 0x13fff94#32 4 = e3)
    (hd0 : read U.mem 0x1401000#32 4 = d0) (hd1 : read U.mem 0x1401004#32 4 = d1)
    (hmain : CodeAt U 0x38#32 codeM) (hlen : codeM.length = 98)
    (hb5 : (codeM.drop 82).take 15 = (Code.main.drop 82).take 15)
    (j5 : Word) (hj5 : codeM[97]? = some j5) (dj5 : decode j5 = some (.jal 1#5 (Af - 0x1bc#32)))
    (hfin : CodeAt U Af Code.finish_success) (hext : CodeAt U (Af + 0x78#32) Code.finish_success_extended) :
    ∃ m W, run m U = some W ∧ W.pc = Af + 0x78#32 + 0x80#32 ∧ W.getReg 10#5 = c ∧ W.getReg 11#5 = p ∧
      W.getReg 12#5 = e0 ∧ W.getReg 13#5 = e1 ∧ W.getReg 14#5 = e2 ∧ W.getReg 15#5 = e3 ∧
      W.getReg 16#5 = d0 ∧ W.getReg 17#5 = d1 ∧
      (∀ i : Reg, 18 ≤ i.toNat → i.toNat ≤ 25 → W.getReg i = 0) ∧
      (∀ b : Word, b.toNat < ROM_END → W.mem b = U.mem b) := by
  have hl : Code.main.length = 98 := by decide +kernel
  have lf : Code.finish_success.length = 30 := by decide +kernel
  have le : Code.finish_success_extended.length = 33 := by decide +kernel
  obtain ⟨_, e97⟩ := List.getElem?_eq_some_iff.mp hj5
  have h2n : (U.getReg 2#5).toNat = 0x13fff80 := by rw [h2]; rfl
  have h19n : (U.getReg 19#5).toNat = 0x1401000 := by rw [h19]; rfl
  simp only [ROM_END, RAM_END] at *
  have hc5 : CodeAt U (0x38#32 + BitVec.ofNat 32 (4 * 82)) ((Code.main.drop 82).take 15) :=
    hb5 ▸ codeAt_take (codeAt_drop hmain 82 (by rw [hlen]; bv_omega)) 15
  obtain ⟨T5, hrun5, hrel5, hrom5, hout5, -⟩ := block_jal _ Main5.instrs Main5.σ U _ (Af - 0x1bc#32) [rF, rBl]
    [] Main5.dec Main5.run (by rw [hpc]; decide) (by decide) (by simp [hl, ROM_END]) hc5 j5
    (by
      rw [show ((Code.main.drop 82).take 15).length = 15 by decide +kernel,
        show (0x38#32 + BitVec.ofNat 32 (4 * 82) + BitVec.ofNat 32 (4 * 15) : Word) =
          0x38#32 + BitVec.ofNat 32 (4 * 97) by decide]
      exact (hmain 97 (by omega)).trans e97)
    dj5 (by simp; bv_omega) (by sym_side) (by simp) (by decide +kernel)
  simp only [List.length_take, List.length_drop, hl, show min 15 (98 - 82) = 15 from rfl] at hrun5
  set S1 := (T5.setPC (0x38#32 + BitVec.ofNat 32 (4 * 82) + BitVec.ofNat 32 (4 * 15) + (Af - 0x1bc#32))).setReg 1#5
    (0x38#32 + BitVec.ofNat 32 (4 * 82) + BitVec.ofNat 32 (4 * 15) + 4) with hS1
  have j1 : ∀ r : Reg, r ≠ 1#5 → S1.getReg r = T5.getReg r := fun r hr => by rw [hS1, jal_getReg _ _ _ _ hr]
  have hpc1 : S1.pc = Af := by rw [hS1, jal_pc]; bv_omega
  have s1rom : ∀ b : Word, b.toNat < 4194304 → S1.mem b = U.mem b := fun b hb => by
    rw [hS1, jal_mem]; exact hrom5 b (by simp only [ROM_END]; omega)
  have s1sp : S1.getReg 2#5 = 0x13fff80#32 := by
    rw [j1 _ (by decide), hrel5.reg_same _ Main5.run _ (by decide +kernel), h2]
  have s1a0 : S1.getReg 10#5 = 0x13fffa8#32 := by
    rw [j1 _ (by decide), hrel5.reg_addr _ Main5.run 10#5 2 40#32 (by decide) (by decide +kernel) (by decide +kernel),
      show (BitVec.ofNat 5 2 : Reg) = 2#5 from rfl, h2]; rfl
  -- the stored outputs
  have ld : ∀ i b (k : Word), b < 32 → i < Main5.σ.pool.len → nodeAt Main5.σ.pool i = .load 4 true b k →
      Main5.σ.pool.val (ctxOf U) i = read U.mem (U.getReg (BitVec.ofNat 5 b) + k) 4 :=
    fun i b k hb hi h => load_val _ _ Main5.run U i b k true hb hi h
  have st : ∀ (k : Word) (i : Nat) (v : Word), outOK Main5.σ [rF, rBl] [] 2 k = true → outNode Main5.σ 2 k = i →
      Main5.σ.pool.val (ctxOf U) i = v → read S1.mem (0x13fff80#32 + k) 4 = v := fun k i v h hn hv => by
    rw [hS1, jal_mem, ← h2, ← hv, ← hn]; exact hout5 2 k (by decide) h
  have w0 := st 40#32 9 c (by decide +kernel) (by decide +kernel) (by rw [val_init _ _ Main5.run U 9 (by decide)]; exact h9)
  have w1 := st 44#32 18 p (by decide +kernel) (by decide +kernel) (by rw [val_init _ _ Main5.run U 18 (by decide)]; exact h18)
  have w2 := st 48#32 32 e0 (by decide +kernel) (by decide +kernel)
    (by rw [ld 32 2 8#32 (by decide) (by decide +kernel) (by decide +kernel), show (BitVec.ofNat 5 2 : Reg) = 2#5 from rfl, h2]; exact he0)
  have w3 := st 52#32 33 e1 (by decide +kernel) (by decide +kernel)
    (by rw [ld 33 2 12#32 (by decide) (by decide +kernel) (by decide +kernel), show (BitVec.ofNat 5 2 : Reg) = 2#5 from rfl, h2]; exact he1)
  have w4 := st 56#32 34 e2 (by decide +kernel) (by decide +kernel)
    (by rw [ld 34 2 16#32 (by decide) (by decide +kernel) (by decide +kernel), show (BitVec.ofNat 5 2 : Reg) = 2#5 from rfl, h2]; exact he2)
  have w5 := st 60#32 35 e3 (by decide +kernel) (by decide +kernel)
    (by rw [ld 35 2 20#32 (by decide) (by decide +kernel) (by decide +kernel), show (BitVec.ofNat 5 2 : Reg) = 2#5 from rfl, h2]; exact he3)
  have w6 := st 64#32 36 d0 (by decide +kernel) (by decide +kernel)
    (by rw [ld 36 19 0#32 (by decide) (by decide +kernel) (by decide +kernel), show (BitVec.ofNat 5 19 : Reg) = 19#5 from rfl, h19]; exact hd0)
  have w7 := st 68#32 37 d1 (by decide +kernel) (by decide +kernel)
    (by rw [ld 37 19 4#32 (by decide) (by decide +kernel) (by decide +kernel), show (BitVec.ofNat 5 19 : Reg) = 19#5 from rfl, h19]; exact hd1)
  simp only [BitVec.reduceAdd] at w0 w1 w2 w3 w4 w5 w6 w7
  -- `zksync_os_finish_success`, then `zksync_os_finish_success_extended`
  obtain ⟨m1, S2, hrun1, hpc2, h22, h102, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15,
    hrom2⟩ := finish_success_run Af hAf (by omega) S1 (codeAt_of_rom hfin (by rw [lf]; simp only [ROM_END]; omega) s1rom)
      hpc1 0x13fffa8#32 s1a0 c p e0 e1 e2 e3 d0 d1 w0 w1 w2 w3 w4 w5 w6 w7
      (by rw [s1sp]; decide) (by rw [s1sp]; decide) (by rw [s1sp]; decide) (by decide) (by decide)
  rw [s1sp] at h22 h102 f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
  simp only [BitVec.reduceAdd] at h22 h102 f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
  have s2rom : ∀ b : Word, b.toNat < 4194304 → S2.mem b = U.mem b := fun b hb => by
    rw [hrom2 b (by simp only [ROM_END]; omega), s1rom b hb]
  obtain ⟨m2, W, hrun2, hpcW, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25,
    hromW⟩ := finish_extended_run (Af + 0x78#32) (by bv_omega) (by bv_omega) S2
      (codeAt_of_rom hext (by rw [le]; simp only [ROM_END]; bv_omega) s2rom) hpc2 (by rw [h102, h22]; rfl)
      c p e0 e1 e2 e3 d0 d1 0 0 0 0 0 0 0 0
      (by rw [h22]; exact f0) (by rw [h22]; exact f1) (by rw [h22]; exact f2) (by rw [h22]; exact f3)
      (by rw [h22]; exact f4) (by rw [h22]; exact f5) (by rw [h22]; exact f6) (by rw [h22]; exact f7)
      (by rw [h22]; exact f8) (by rw [h22]; exact f9) (by rw [h22]; exact f10) (by rw [h22]; exact f11)
      (by rw [h22]; exact f12) (by rw [h22]; exact f13) (by rw [h22]; exact f14) (by rw [h22]; exact f15)
      (by rw [h22]; decide) (by rw [h22]; decide) (by rw [h22]; decide)
  refine ⟨_, W, run_trans (run_trans hrun5 hrun1) hrun2, hpcW, r10, r11, r12, r13, r14, r15, r16, r17, ?_, ?_⟩
  · intro i h1 h2'
    have : i = 18#5 ∨ i = 19#5 ∨ i = 20#5 ∨ i = 21#5 ∨ i = 22#5 ∨ i = 23#5 ∨ i = 24#5 ∨ i = 25#5 := by bv_omega
    rcases this with h|h|h|h|h|h|h|h <;> subst h <;> assumption
  · intro b hb
    rw [hromW b hb, s2rom b hb]

end RV
