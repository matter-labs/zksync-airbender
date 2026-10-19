import Slop.RV.Main.A
import Slop.RV.Ext4Call
import Slop.RV.Main.Blake

/-! `main`, second part (both images): `ext4_poly` (any implementation of its contract) and the Blake2s part (any
proof of `MainBlakeOK`); from `main + 0x68` to `main + 0x14c`. -/

namespace RV
open _root_.RV.Sym Spec
set_option maxHeartbeats 0

namespace MainB
abbrev rF : Region := ⟨2, 0, 112, 16⟩
end MainB
open MainB

theorem main_b (T : State) (codeM codeB : List Word) (Aep Ab : Word) (codeEP : List Word)
    (calleesEP : List (Word × List Word)) (FEP : Nat)
    (hEP : ImplementsAtW Aep codeEP calleesEP FEP e4polyPre 16 e4polyPost)
    (hEPr : Aep.toNat + 4 * codeEP.length ≤ 4194304) (hEP4 : Aep.toNat % 4 = 0) (hFEP : FEP ≤ 0x100000)
    (hcalr : ∀ c ∈ calleesEP, c.1.toNat + 4 * c.2.length ≤ 4194304)
    (hBl : MainBlakeOK codeM codeB Ab) (hAbr : Ab.toNat + 4 * codeB.length ≤ 4194304)
    (c p x y0 y1 y2 y3 : Word)
    (hpc : T.pc = 0xa0#32) (h2 : T.getReg 2#5 = 0x13fff80#32) (h9 : T.getReg 9#5 = c) (h10 : T.getReg 10#5 = p)
    (h20 : T.getReg 20#5 = x) (h21 : T.getReg 21#5 = y0)
    (h22 : T.getReg 22#5 = y1) (h23 : T.getReg 23#5 = y2) (h24 : T.getReg 24#5 = y3)
    (htab : CodeMem T.mem (0x1400000#32 + BitVec.ofNat 32 0x190) Code.COEFFS4)
    (hz : ∀ a : Word, 0x1401000 ≤ a.toNat → a.toNat < 0x1401100 → T.mem a = 0)
    (hmain : CodeAt T 0x38#32 codeM) (hlen : codeM.length = 98)
    (hb3 : (codeM.drop 26).take 7 = (Code.main.drop 26).take 7)
    (j3 : Word) (hj3 : codeM[33]? = some j3) (dj3 : decode j3 = some (.jal 1#5 (Aep - 0xbc#32)))
    (hEPc : CodeAt T Aep codeEP) (hcal : ∀ c ∈ calleesEP, CodeAt T c.1 c.2)
    (hbl : CodeAt T Ab codeB)
    (hy0 : y0.toNat < BabyBearP) (hy1 : y1.toNat < BabyBearP) (hy2 : y2.toNat < BabyBearP)
    (hy3 : y3.toNat < BabyBearP) :
    ∃ m U, run m T = some U ∧ U.pc = 0x14c#32 ∧ U.getReg 2#5 = 0x13fff80#32 ∧ U.getReg 9#5 = c ∧
      U.getReg 18#5 = p ∧ U.getReg 19#5 = 0x1401000#32 ∧
      canon4 U.mem 0x13fff88#32 ∧
      limbsAt U.mem 0x13fff88#32 = poly4 (ofLimbs (y0.toNat : F) (y1.toNat : F) (y2.toNat : F) (y3.toNat : F)) ∧
      wordsAt U.mem 0x1401000#32 8 = blake5 #v[x, y0, y1, y2, y3] ∧
      CodeMem U.mem (0x1400000#32 + BitVec.ofNat 32 0x190) Code.COEFFS4 ∧
      (∀ b : Word, b.toNat < ROM_END → U.mem b = T.mem b) := by
  have hl : Code.main.length = 98 := by decide +kernel
  obtain ⟨_, e33⟩ := List.getElem?_eq_some_iff.mp hj3
  have h2n : (T.getReg 2#5).toNat = 0x13fff80 := by rw [h2]; rfl
  simp only [ROM_END, RAM_END] at *
  ------------------------------------------------------------------ `ext4_poly`
  have hc3 : CodeAt T (0x38#32 + BitVec.ofNat 32 (4 * 26)) ((Code.main.drop 26).take 7) :=
    hb3 ▸ codeAt_take (codeAt_drop hmain 26 (by rw [hlen]; bv_omega)) 7
  obtain ⟨T3, hrun3, hrel3, hrom3, hout3, hfr3⟩ := block_jal _ Main3.instrs Main3.σ T _ (Aep - 0xbc#32) [rF] []
    Main3.dec Main3.run (by rw [hpc]; decide) (by decide) (by simp [hl, ROM_END]) hc3 j3
    (by
      rw [show ((Code.main.drop 26).take 7).length = 7 by decide +kernel,
        show (0x38#32 + BitVec.ofNat 32 (4 * 26) + BitVec.ofNat 32 (4 * 7) : Word) =
          0x38#32 + BitVec.ofNat 32 (4 * 33) by decide]
      exact (hmain 33 (by omega)).trans e33)
    dj3 (by simp; bv_omega) (by sym_side) (by simp) (by decide +kernel)
  simp only [List.length_take, List.length_drop, hl, show min 7 (98 - 26) = 7 from rfl] at hrun3
  set S1 := (T3.setPC (0x38#32 + BitVec.ofNat 32 (4 * 26) + BitVec.ofNat 32 (4 * 7) + (Aep - 0xbc#32))).setReg 1#5
    (0x38#32 + BitVec.ofNat 32 (4 * 26) + BitVec.ofNat 32 (4 * 7) + 4) with hS1
  have j1 : ∀ r : Reg, r ≠ 1#5 → S1.getReg r = T3.getReg r := fun r hr => by rw [hS1, jal_getReg _ _ _ _ hr]
  have hpc1 : S1.pc = Aep := by rw [hS1, jal_pc]; bv_omega
  have s1rom : ∀ b : Word, b.toNat < 4194304 → S1.mem b = T.mem b := fun b hb => by
    rw [hS1, jal_mem]; exact hrom3 b (by simp only [ROM_END]; omega)
  have s1sp : S1.getReg 2#5 = 0x13fff80#32 := by
    rw [j1 _ (by decide), hrel3.reg_same _ Main3.run _ (by decide +kernel), h2]
  have s1a0 : S1.getReg 10#5 = 0x13fff88#32 := by
    rw [j1 _ (by decide), hrel3.reg_addr _ Main3.run 10#5 2 8#32 (by decide) (by decide +kernel) (by decide +kernel),
      show (BitVec.ofNat 5 2 : Reg) = 2#5 from rfl, h2]; rfl
  have s1a1 : S1.getReg 11#5 = 0x13fffa8#32 := by
    rw [j1 _ (by decide), hrel3.reg_addr _ Main3.run 11#5 2 40#32 (by decide) (by decide +kernel) (by decide +kernel),
      show (BitVec.ofNat 5 2 : Reg) = 2#5 from rfl, h2]; rfl
  -- the stored `y`, and memory outside `main`'s frame unchanged
  have st : ∀ (k : Word) (i : Nat) (v : Word), outOK Main3.σ [rF] [] 2 k = true → outNode Main3.σ 2 k = i →
      i < 32 → T.getReg (BitVec.ofNat 5 i) = v → read S1.mem (0x13fff80#32 + k) 4 = v := fun k i v h hn hi hv => by
    rw [hS1, jal_mem, ← h2, ← hv, ← val_init _ _ Main3.run T i hi, ← hn]; exact hout3 2 k (by decide) h
  have sy0 := st 40#32 21 y0 (by decide +kernel) (by decide +kernel) (by decide) h21
  have sy1 := st 44#32 22 y1 (by decide +kernel) (by decide +kernel) (by decide) h22
  have sy2 := st 48#32 23 y2 (by decide +kernel) (by decide +kernel) (by decide) h23
  have sy3 := st 52#32 24 y3 (by decide +kernel) (by decide +kernel) (by decide) h24
  simp only [BitVec.reduceAdd] at sy0 sy1 sy2 sy3
  have s1out : ∀ a : Word, (a.toNat < 0x13fff80 ∨ 0x13ffff0 ≤ a.toNat) → S1.mem a = T.mem a := fun a ha => by
    rw [hS1, jal_mem]
    apply hfr3 [⟨2, 0, 112, 1⟩] (by decide +kernel) (by sym_side) a
    intro R hR; simp only [List.mem_singleton] at hR; subst hR
    simp only [Region.Outside, show (BitVec.ofNat 5 2 : Reg) = 2#5 from rfl]; omega
  obtain ⟨n2, S2, hrun2, hpc2, hpost2, hcs2, hmem2⟩ := hEP S1 hpc1
    (fun c hc => codeAt_of_rom (hcal c hc) (by have := hcalr c hc; simp only [ROM_END]; omega) s1rom)
    ⟨(by rw [hpc1]; exact codeAt_of_rom hEPc (by simp only [ROM_END]; omega) s1rom),
      (by rw [hpc1]; exact hEP4), (by rw [hpc1]; simp only [ROM_END]; omega),
      (by show (S1.getReg 1#5).toNat % 4 = 0; rw [hS1, jal_getReg1]; decide),
      (by show (S1.getReg 2#5).toNat % 16 = 0; rw [s1sp]; decide),
      (by show ROM_END + FEP ≤ (S1.getReg 2#5).toNat; rw [s1sp]; simp only [ROM_END]; bv_omega),
      (by show (S1.getReg 2#5).toNat ≤ RAM_END; rw [s1sp]; decide)⟩
    (by
      simp only [e4polyPre, argOk, RAM_END, s1sp, s1a0, s1a1, canon4]
      refine ⟨by decide, by decide, ?_, fun i hi => ?_, by decide⟩
      · simp only [BitVec.reduceAdd, sy0, sy1, sy2, sy3]
        exact ⟨hy0, hy1, hy2, hy3⟩
      · rw [read_congr _ T.mem _ 4 (fun j hj => s1out _ (by right; rw [coeffs4_length] at hi; bv_omega))]
        exact htab i hi)
  replace hpc2 : S2.pc = S1.getReg 1#5 := hpc2
  replace hcs2 : ∀ i, calleeSaved i → S2.getReg i = S1.getReg i := hcs2
  replace hmem2 : ∀ a : Word, a.toNat + FEP < (S1.getReg 2#5).toNat ∨ (S1.getReg 2#5).toNat ≤ a.toNat →
      a.toNat < (S1.getReg 10#5).toNat ∨ (S1.getReg 10#5).toNat + 16 ≤ a.toNat → S2.mem a = S1.mem a := hmem2
  rw [s1sp, s1a0] at hmem2
  simp only [e4polyPost, s1a0, s1a1] at hpost2
  obtain ⟨hcanE, hvalE⟩ := hpost2
  have hyl : limbsAt S1.mem 0x13fffa8#32 = ofLimbs (y0.toNat : F) (y1.toNat : F) (y2.toNat : F) (y3.toNat : F) := by
    simp only [limbsAt, BitVec.reduceAdd, sy0, sy1, sy2, sy3]
  rw [hyl] at hvalE
  have s2rom : ∀ b : Word, b.toNat < 4194304 → S2.mem b = T.mem b := fun b hb => by
    rw [hmem2 b (by left; bv_omega) (by left; bv_omega), s1rom b hb]
  have s2bl : ∀ a : Word, 0x1401000 ≤ a.toNat → a.toNat < 0x1401100 → S2.mem a = T.mem a := fun a h1 h2' => by
    rw [hmem2 a (by right; bv_omega) (by right; bv_omega), s1out a (by right; omega)]
  have s2cs : ∀ r : Reg, calleeSaved r → (Main3.σ.reg r).val = r.toNat → S2.getReg r = T.getReg r := fun r h hv => by
    rw [hcs2 r h, j1 r (by rintro rfl; simp [calleeSaved] at h), hrel3.reg_same _ Main3.run r hv]
  have s2r : ∀ r : Reg, calleeSaved r → S2.getReg r = T3.getReg r := fun r h => by
    rw [hcs2 r h, j1 r (by rintro rfl; simp [calleeSaved] at h)]
  have s2sp : S2.getReg 2#5 = 0x13fff80#32 := (hcs2 _ (by rv_callee_saved)).trans s1sp
  have hpc2' : S2.pc = 0x38#32 + BitVec.ofNat 32 (4 * 34) := by rw [hpc2, hS1, jal_getReg1]; rfl
  ------------------------------------------------------------------ the Blake2s part
  obtain ⟨n4, U, hrun5, hpc5, hu19, hcs5, hdig, hmem5, hrom5⟩ := hBl S2 (by rw [hpc2']; rfl)
    (codeAt_of_rom hmain (by rw [hlen]; simp only [ROM_END]; decide) s2rom)
    (codeAt_of_rom hbl (by simp only [ROM_END]; omega) s2rom) s2sp
    (fun a h1 h2' => (s2bl a h1 h2').trans (hz a h1 h2'))
  -- `e` (the `ext4_poly` result) at `sp + 8`: untouched since
  have ue : ∀ a : Word, 0x13fff88 ≤ a.toNat → a.toNat < 0x13fff98 → U.mem a = S2.mem a := fun a h1 h2' =>
    hmem5 a (by omega) (by left; omega)
  have ur : ∀ k : Word, k.toNat ≤ 12 → read U.mem (0x13fff88#32 + k) 4 = read S2.mem (0x13fff88#32 + k) 4 :=
    fun k hk => read_congr _ _ _ _ (fun j hj => ue _ (by bv_omega) (by bv_omega))
  have u0 : read U.mem 0x13fff88#32 4 = read S2.mem 0x13fff88#32 4 :=
    read_congr _ _ _ _ (fun j hj => ue _ (by bv_omega) (by bv_omega))
  have utab : ∀ a : Word, 0x1400190 ≤ a.toNat → a.toNat < 0x1400390 → U.mem a = T.mem a := fun a h1 h2' => by
    rw [hmem5 a (by omega) (by left; omega), hmem2 a (by right; bv_omega) (by right; bv_omega),
      s1out a (by right; omega)]
  have ucs : ∀ r : Reg, calleeSaved r → r ≠ 19#5 → (Main3.σ.reg r).val = r.toNat → U.getReg r = T.getReg r :=
    fun r h h19 hv => by rw [hcs5 r h h19, s2cs r h hv]
  refine ⟨_, U, run_trans (run_trans hrun3 hrun2) hrun5, hpc5, ?_, ?_, ?_, hu19, ?_, ?_, ?_, fun i hi => ?_, ?_⟩
  · rw [hcs5 _ (by rv_callee_saved) (by decide), s2sp]
  · rw [ucs _ (by rv_callee_saved) (by decide) (by decide +kernel), h9]
  · rw [hcs5 _ (by rv_callee_saved) (by decide), s2r _ (by rv_callee_saved),
      hrel3.reg_var _ Main3.run _ 10 (by decide) (by decide +kernel)]
    exact h10
  · simp only [canon4] at hcanE ⊢
    rw [u0, ur 4#32 (by decide), ur 8#32 (by decide), ur 12#32 (by decide)]; exact hcanE
  · simp only [limbsAt] at hvalE ⊢
    rw [u0, ur 4#32 (by decide), ur 8#32 (by decide), ur 12#32 (by decide)]; exact hvalE
  · rw [hdig, s2cs _ (by rv_callee_saved) (by decide +kernel), s2cs _ (by rv_callee_saved) (by decide +kernel),
      s2cs _ (by rv_callee_saved) (by decide +kernel), s2cs _ (by rv_callee_saved) (by decide +kernel),
      s2cs _ (by rv_callee_saved) (by decide +kernel), h20, h21, h22, h23, h24]
  · rw [read_congr _ T.mem _ 4 (fun j hj => utab _ (by rw [coeffs4_length] at hi; bv_omega)
      (by rw [coeffs4_length] at hi; bv_omega))]
    exact htab i hi
  · intro b hb
    rw [hrom5 b (by simp only [ROM_END]; omega), s2rom b hb]

end RV
