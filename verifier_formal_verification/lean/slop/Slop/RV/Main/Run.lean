import Slop.RV.Start
import Slop.RV.Main.C
import Slop.RV.PolyZMod
import Slop.RV.Halt
import Human.Theorems

/-! The whole program for either image, from reset, given the code at its addresses: `_start` → `main` (parts A, B,
C) → the final self-jump. The images instantiate it (`FinalPlain`, `FinalMop`). -/

namespace RV
open Spec
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem main_run (s : State) (codeM codeI codeEP : List Word) (calleesEP : List (Word × List Word)) (FEP : Nat)
    (Ai Ac Ap Aep Ab Af src : Word) (x y0 y1 y2 y3 : Word)
    (hI : InitOK Ai src codeI) (hIl : codeI.length = 34) (hAi : Ai.toNat % 4 = 0)
    (hAir : Ai.toNat + 136 + 4 * 1676 ≤ 4194304)
    (hAc : Ac.toNat + 0x6c + 36 ≤ 4194304) (hAc4 : Ac.toNat % 4 = 0)
    (hAp : 256 ≤ Ap.toNat) (hAp4 : Ap.toNat % 4 = 0) (hApr : Ap.toNat + 4 * Code.poly_eval.length ≤ 4194304)
    (hsrc : src.toNat + 912 ≤ 4194304)
    (hEP : ImplementsAtW Aep codeEP calleesEP FEP e4polyPre 16 e4polyPost)
    (hEPr : Aep.toNat + 4 * codeEP.length ≤ 4194304) (hEP4 : Aep.toNat % 4 = 0) (hFEP : FEP ≤ 0x100000)
    (hcalr : ∀ c ∈ calleesEP, c.1.toNat + 4 * c.2.length ≤ 4194304)
    (hAb : Ab.toNat % 4 = 0) (hAbr : Ab.toNat + 4 * Code.blake2s_compress.length ≤ 4194304)
    (hAf : Af.toNat % 4 = 0) (hAfr : Af.toNat + 0x78 + 0x84 ≤ 4194304)
    (hlen : codeM.length = 85)
    (hb0 : codeM.take 12 = Code.main.take 12) (hb1 : (codeM.drop 13).take 8 = (Code.main.drop 13).take 8)
    (hb2 : (codeM.drop 22).take 5 = (Code.main.drop 22).take 5)
    (hb3 : (codeM.drop 28).take 7 = (Code.main.drop 28).take 7)
    (hb4 : (codeM.drop 36).take 32 = (Code.main.drop 36).take 32)
    (hb5 : (codeM.drop 69).take 15 = (Code.main.drop 69).take 15)
    (dj0 : decode codeM[12]! = some (.jal 1#5 (Ai - 0x68#32)))
    (dj1 : decode codeM[21]! = some (.jal 1#5 (Ac - 0x8c#32)))
    (dj2 : decode codeM[27]! = some (.jal 1#5 (Ap - 0xa4#32)))
    (dj3 : decode codeM[35]! = some (.jal 1#5 (Aep - 0xc4#32)))
    (dj4 : decode codeM[68]! = some (.jal 1#5 (Ab - 0x148#32)))
    (dj5 : decode codeM[84]! = some (.jal 1#5 (Af - 0x188#32)))
    (hpc : s.pc = 0) (cStart : CodeAt s 0 Code.start) (cMain : CodeAt s 0x38#32 codeM)
    (cInit : CodeAt s Ai codeI) (cMemcpy : CodeAt s (Ai + 136#32) Code.memcpy)
    (cComb : CodeAt s Ac Code.combine) (cInc : CodeAt s (Ac + 0x6c#32) Code.inc)
    (cDbl : CodeAt s (Ac + 0x48#32) Code.double)
    (cPoly : CodeAt s Ap Code.poly_eval) (cMul : CodeAt s (Ap + 4294967236#32) Code.mul_mod)
    (cAdd : CodeAt s (Ap + 4294967184#32) Code.add_mod)
    (cCoef : CodeAt s src Code.COEFFS) (cCoef4 : CodeAt s (src + BitVec.ofNat 32 0x190) Code.COEFFS4)
    (cEP : CodeAt s Aep codeEP) (cCal : ∀ c ∈ calleesEP, CodeAt s c.1 c.2)
    (cBl : CodeAt s Ab Code.blake2s_compress)
    (cFin : CodeAt s Af Code.finish_success) (cExt : CodeAt s (Af + 0x78#32) Code.finish_success_extended)
    (hram : RamZeroExceptInput 0x1401000 20 s)
    (hx : read s.mem 0x1401000#32 4 = x) (hy0 : read s.mem 0x1401004#32 4 = y0)
    (hy1 : read s.mem 0x1401008#32 4 = y1) (hy2 : read s.mem 0x140100c#32 4 = y2)
    (hy3 : read s.mem 0x1401010#32 4 = y3) (hxP : x.toNat ≤ P)
    (hy0p : y0.toNat < BabyBearP) (hy1p : y1.toNat < BabyBearP) (hy2p : y2.toNat < BabyBearP)
    (hy3p : y3.toNat < BabyBearP) :
    ∃ m W, run m s = some W ∧ W.pc = Af + 0x78#32 + 0x80#32 ∧
      W.getReg 10#5 = combine x ∧ (W.getReg 11#5).toNat ≤ P ∧
      ((W.getReg 11#5).toNat : ZMod P) = poly (x.toNat : ZMod P) ∧
      (∀ i : Reg, 12 ≤ i.toNat → i.toNat ≤ 15 → (W.getReg i).toNat < BabyBearP) ∧
      ofLimbs (bb (W.getReg 12)) (bb (W.getReg 13)) (bb (W.getReg 14)) (bb (W.getReg 15)) =
        poly4 (ofLimbs (bb y0) (bb y1) (bb y2) (bb y3)) ∧
      W.getReg 16 = (blake5 #v[x, y0, y1, y2, y3])[0] ∧ W.getReg 17 = (blake5 #v[x, y0, y1, y2, y3])[1] ∧
      (∀ i : Reg, 18 ≤ i.toNat → i.toNat ≤ 25 → W.getReg i = 0) ∧
      (∀ b : Word, b.toNat < ROM_END → W.mem b = s.mem b) := by
  have rd0 := fun i (h : i < 85) => cMain i (by omega)
  -- `_start`
  obtain ⟨m0, S0, hrun0, hpc0, h20, hra0, hm0⟩ := start_run s hpc cStart
  have hrom0 : ∀ b : Word, b.toNat < ROM_END → S0.mem b = s.mem b := fun b hb =>
    hm0 b (by simp only [ROM_END] at hb; omega)
  have rd : ∀ a : Word, 0x1401000 ≤ a.toNat → a.toNat + 4 ≤ 0x1401014 → read S0.mem a 4 = read s.mem a 4 :=
    fun a h1 h2 => read_congr _ _ _ _ (fun j hj => hm0 _ (by bv_omega))
  have get : ∀ i (h : i < 85), codeM[i]? = some codeM[i]! := fun i h => by
    rw [getElem!_pos codeM i (by omega)]; exact List.getElem?_eq_getElem (by omega)
  -- `main`, part A
  obtain ⟨mA, T, hrunA, hpcT, h2T, h9T, hpT, hpT', h19T, h20T, h21T, h22T, h23T, h24T, htabT, hhiT, hromT⟩ :=
    main_a S0 codeM codeI Ai Ac Ap src x y0 y1 y2 y3 hI hIl hAi hAir hAc hAc4 hAp hAp4 hApr hsrc hpc0 h20 hra0
      (codeAt_of_rom cMain (by rw [hlen]; simp only [ROM_END]; decide) hrom0) hlen hb0 hb1 hb2
      _ _ _ (get 12 (by decide)) (get 21 (by decide)) (get 27 (by decide)) dj0 dj1 dj2
      (codeAt_of_rom cInit (by rw [hIl]; simp only [ROM_END]; omega) hrom0)
      (codeAt_of_rom cMemcpy (by rw [memcpy_length]; simp only [ROM_END]; bv_omega) hrom0)
      (codeAt_of_rom cComb (by simp only [Code.combine, List.length_cons, List.length_nil, ROM_END]; bv_omega) hrom0)
      (codeAt_of_rom cInc (by simp only [Code.inc, List.length_cons, List.length_nil, ROM_END]; bv_omega) hrom0)
      (codeAt_of_rom cDbl (by simp only [Code.double, List.length_cons, List.length_nil, ROM_END]; bv_omega) hrom0)
      (codeAt_of_rom cPoly (by simp only [ROM_END]; omega) hrom0)
      (codeAt_of_rom cMul (by simp only [Code.mul_mod, List.length_cons, List.length_nil, ROM_END]; bv_omega) hrom0)
      (codeAt_of_rom cAdd (by simp only [Code.add_mod, List.length_cons, List.length_nil, ROM_END]; bv_omega) hrom0)
      (codeAt_of_rom cCoef (by rw [coeffs_length]; simp only [ROM_END]; omega) hrom0)
      (codeAt_of_rom cCoef4 (by rw [coeffs4_length]; simp only [ROM_END]; bv_omega) hrom0)
      ((rd _ (by decide) (by decide)).trans hx) ((rd _ (by decide) (by decide)).trans hy0)
      ((rd _ (by decide) (by decide)).trans hy1) ((rd _ (by decide) (by decide)).trans hy2)
      ((rd _ (by decide) (by decide)).trans hy3) hxP
  have hromT' : ∀ b : Word, b.toNat < ROM_END → T.mem b = s.mem b := fun b hb => (hromT b hb).trans (hrom0 b hb)
  -- `main`, part B
  obtain ⟨mB, U, hrunB, hpcU, h2U, h9U, h18U, h20U, hcanU, hvalU, hblU, hromU⟩ :=
    main_b T codeM Aep Ab codeEP calleesEP FEP hEP hEPr hEP4 hFEP hcalr hAb hAbr (3#32 * x + 1#32) (T.getReg 10#5)
      x y0 y1 y2 y3 hpcT h2T h9T rfl h19T h20T h21T h22T h23T h24T htabT
      (fun a h1 h2 => by
        rw [hhiT a (by omega) (by omega), hm0 a (by right; omega)]
        exact hram a (by simp only [ROM_END]; omega) (by simp only [RAM_END]; omega) (by right; omega))
      (codeAt_of_rom cMain (by rw [hlen]; simp only [ROM_END]; decide) hromT') hlen hb3 hb4
      _ _ (get 35 (by decide)) (get 68 (by decide)) dj3 dj4
      (codeAt_of_rom cEP (by simp only [ROM_END]; omega) hromT')
      (fun c hc => codeAt_of_rom (cCal c hc) (by have := hcalr c hc; simp only [ROM_END]; omega) hromT')
      (codeAt_of_rom cBl (by simp only [ROM_END]; omega) hromT') hy0p hy1p hy2p hy3p
  have hromU' : ∀ b : Word, b.toNat < ROM_END → U.mem b = s.mem b := fun b hb => (hromU b hb).trans (hromT' b hb)
  -- `main`, part C and the end
  have lf : Code.finish_success.length = 30 := by decide +kernel
  have le : Code.finish_success_extended.length = 33 := by decide +kernel
  simp only [canon4] at hcanU
  obtain ⟨mC, W, hrunC, hpcW, r10, r11, r12, r13, r14, r15, r16, r17, rz, hromW⟩ :=
    main_c U codeM Af _ _ _ _ _ _ _ _ hAf hAfr hpcU h2U h9U h18U h20U rfl rfl rfl rfl rfl rfl
      (codeAt_of_rom cMain (by rw [hlen]; simp only [ROM_END]; decide) hromU') hlen hb5
      _ (get 84 (by decide)) dj5
      (codeAt_of_rom cFin (by rw [lf]; simp only [ROM_END]; omega) hromU')
      (codeAt_of_rom cExt (by rw [le]; simp only [ROM_END]; bv_omega) hromU')
  have hW : ∀ b : Word, b.toNat < ROM_END → W.mem b = s.mem b := fun b hb => (hromW b hb).trans (hromU' b hb)
  refine ⟨_, W, run_trans (run_trans (run_trans hrun0 hrunA) hrunB) hrunC, hpcW, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rz, hW⟩
  · rw [r10]; rfl
  · rw [r11]; exact hpT
  · rw [r11, ← polyW_zmod, ZMod.natCast_eq_natCast_iff']; exact hpT'
  · intro i h1 h2'
    rcases (by bv_omega : i = 12#5 ∨ i = 13#5 ∨ i = 14#5 ∨ i = 15#5) with h|h|h|h <;> subst h
    · rw [r12]; exact hcanU.1
    · rw [r13]; simpa only [BitVec.add_assoc, BitVec.reduceAdd] using hcanU.2.1
    · rw [r14]; simpa only [BitVec.add_assoc, BitVec.reduceAdd] using hcanU.2.2.1
    · rw [r15]; simpa only [BitVec.add_assoc, BitVec.reduceAdd] using hcanU.2.2.2
  · simp only [limbsAt] at hvalU
    have e12 : W.getReg 12 = _ := r12
    have e13 : W.getReg 13 = _ := r13
    have e14 : W.getReg 14 = _ := r14
    have e15 : W.getReg 15 = _ := r15
    rw [e12, e13, e14, e15]; simpa only [BitVec.add_assoc, BitVec.reduceAdd, bb] using hvalU
  · have e16 : W.getReg 16 = _ := r16
    rw [e16, ← hblU]; simp [wordsAt]
  · have e17 : W.getReg 17 = _ := r17
    rw [e17, ← hblU]; simp [wordsAt]

end RV
