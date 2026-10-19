import Slop.RV.Start
import Slop.RV.Main.C
import Slop.RV.Main.F
import Slop.RV.Main.M
import Slop.RV.PolyZMod
import Slop.RV.Input
import Slop.RV.Halt
import Human.Theorems

/-! The whole program for either image, from reset, given the code at its addresses: `_start` → `main` (`init`, the
input reads, parts A, B, the claim reads, `fs_check`, the Merkle path, part C) → the final self-jump, or stuck in
`fs_check` (a wrong claim) or `merkle_check` (a wrong root). The images instantiate it (`FinalPlain`, `FinalMop`). Between the reads, the runs are those with the
input empty (`run_lift`): they read no input, whatever the functions do. -/

namespace RV
open Spec
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem main_run (s : State) (codeM codeI codeEP codeB : List Word) (calleesEP : List (Word × List Word)) (FEP : Nat)
    (codeF : List Word) (Ai Ac Ap Aep Ab Af Afs Aerr src : Word) (x y0 y1 y2 y3 v0 v1 v2 v3 : Word)
    (hI : InitOK Ai src codeI) (hIl : codeI.length = 34) (hAi : Ai.toNat % 4 = 0)
    (hAir : Ai.toNat + 136 + 4 * 1676 ≤ 4194304)
    (hAc : Ac.toNat + 0x6c + 36 ≤ 4194304) (hAc4 : Ac.toNat % 4 = 0)
    (hAp : 256 ≤ Ap.toNat) (hAp4 : Ap.toNat % 4 = 0) (hApr : Ap.toNat + 4 * Code.poly_eval.length ≤ 4194304)
    (hsrc : src.toNat + 912 ≤ 4194304)
    (hEP : ImplementsAtW Aep codeEP calleesEP FEP e4polyPre 16 e4polyPost)
    (hEPr : Aep.toNat + 4 * codeEP.length ≤ 4194304) (hEP4 : Aep.toNat % 4 = 0) (hFEP : FEP ≤ 0x100000)
    (hcalr : ∀ c ∈ calleesEP, c.1.toNat + 4 * c.2.length ≤ 4194304)
    (hBl : MainBlakeOK codeM codeB Ab) (hAbr : Ab.toNat + 4 * codeB.length ≤ 4194304)
    (hAf : Af.toNat % 4 = 0) (hAfr : Af.toNat + 0x78 + 0x84 ≤ 4194304)
    (hAfs : Afs.toNat % 4 = 0) (hAfsr : Afs.toNat + 4 * 113 ≤ 4194304) (hlenF : codeF.length = 113)
    (hbFA : codeF.take 53 = Code.fs_check.take 53) (hbFB : (codeF.drop 54).take 58 = (Code.fs_check.drop 54).take 58)
    (djF53 : decode codeF[53]! = some (.jal 1#5 (Aep - (Afs + BitVec.ofNat 32 (4 * 53)))))
    (djF112 : decode codeF[112]! = some (.jal 1#5 (Aerr - (Afs + BitVec.ofNat 32 (4 * 112)))))
    (hAerr : Aerr.toNat % 4 = 0) (hAerrr : Aerr.toNat + 24 ≤ 4194304)
    (Am : Word) (codeS : List Word) (calleesS : List (Word × List Word)) (FS al len : Nat)
    (hS : ImplementsAtW (Am + 0x1bc#32) codeS calleesS FS (merklePre al len) len merklePost)
    (hAm : Am.toNat % 4 = 0) (hAmr : Am.toNat + 4 * 111 + 0x21c + 24 ≤ ROM_END)
    (hSr : (Am + 0x1bc#32).toNat + 4 * codeS.length ≤ ROM_END)
    (hcalrS : ∀ c ∈ calleesS, c.1.toNat + 4 * c.2.length ≤ ROM_END)
    (hMal : MERKLE.toNat % al = 0) (hlen256 : len ≤ 256) (hlen32 : 32 ≤ len)
    (hFS : ROM_END + 96 + FS ≤ 0x13fff80) (hFS16 : 16 ≤ FS)
    (hlen : codeM.length = 98)
    (hb0 : codeM.take 12 = Code.main.take 12) (hbR : (codeM.drop 13).take 5 = (Code.main.drop 13).take 5)
    (hb1 : (codeM.drop 18).take 1 = (Code.main.drop 18).take 1)
    (hb2 : (codeM.drop 20).take 5 = (Code.main.drop 20).take 5)
    (hb3 : (codeM.drop 26).take 7 = (Code.main.drop 26).take 7)
    (hbV : (codeM.drop 69).take 4 = (Code.main.drop 69).take 4)
    (hbF : (codeM.drop 73).take 6 = (Code.main.drop 73).take 6)
    (hbM : (codeM.drop 80).take 1 = (Code.main.drop 80).take 1)
    (hb5 : (codeM.drop 82).take 15 = (Code.main.drop 82).take 15)
    (dj0 : decode codeM[12]! = some (.jal 1#5 (Ai - 0x68#32)))
    (dj1 : decode codeM[19]! = some (.jal 1#5 (Ac - 0x84#32)))
    (dj2 : decode codeM[25]! = some (.jal 1#5 (Ap - 0x9c#32)))
    (dj3 : decode codeM[33]! = some (.jal 1#5 (Aep - 0xbc#32)))
    (djf : decode codeM[79]! = some (.jal 1#5 (Afs - 0x174#32)))
    (djm : decode codeM[81]! = some (.jal 1#5 (Am - 0x17c#32)))
    (dj5 : decode codeM[97]! = some (.jal 1#5 (Af - 0x1bc#32)))
    (hpc : s.pc = 0) (cStart : CodeAt s 0 Code.start) (cMain : CodeAt s 0x38#32 codeM)
    (cInit : CodeAt s Ai codeI) (cMemcpy : CodeAt s (Ai + 136#32) Code.memcpy)
    (cComb : CodeAt s Ac Code.combine) (cInc : CodeAt s (Ac + 0x6c#32) Code.inc)
    (cDbl : CodeAt s (Ac + 0x48#32) Code.double)
    (cPoly : CodeAt s Ap Code.poly_eval) (cMul : CodeAt s (Ap + 4294967236#32) Code.mul_mod)
    (cAdd : CodeAt s (Ap + 4294967184#32) Code.add_mod)
    (cCoef : CodeAt s src Code.COEFFS) (cCoef4 : CodeAt s (src + BitVec.ofNat 32 0x190) Code.COEFFS4)
    (cEP : CodeAt s Aep codeEP) (cCal : ∀ c ∈ calleesEP, CodeAt s c.1 c.2)
    (cBl : CodeAt s Ab codeB)
    (cFin : CodeAt s Af Code.finish_success) (cExt : CodeAt s (Af + 0x78#32) Code.finish_success_extended)
    (cFs : CodeAt s Afs codeF) (cErr : CodeAt s Aerr Code.finish_error)
    (cMc : CodeAt s Am Code.merkle_check) (cMe : CodeAt s (Am + 0x3d4#32) Code.finish_error)
    (cS : CodeAt s (Am + 0x1bc#32) codeS) (cCalS : ∀ c ∈ calleesS, CodeAt s c.1 c.2)
    (root : Vector Word 8) (path : List MerkleStep) (hd : path.length ≤ 32)
    (hram : RamZero s) (rest : List Word) (hin : s.input = x :: y0 :: y1 :: y2 :: y3 :: v0 :: v1 :: v2 :: v3 :: (pathInput root path ++ rest)) (hxP : x.toNat ≤ P)
    (hy0p : y0.toNat < BabyBearP) (hy1p : y1.toNat < BabyBearP) (hy2p : y2.toNat < BabyBearP)
    (hy3p : y3.toNat < BabyBearP) :
    (claimOK #v[x, y0, y1, y2, y3] #v[v0, v1, v2, v3] ∧ pathOK #v[x, y0, y1, y2, y3] root path →
    ∃ m W, run m s = some W ∧ W.pc = Af + 0x78#32 + 0x80#32 ∧
      W.getReg 10#5 = combine x ∧ (W.getReg 11#5).toNat ≤ P ∧
      ((W.getReg 11#5).toNat : ZMod P) = poly (x.toNat : ZMod P) ∧
      (∀ i : Reg, 12 ≤ i.toNat → i.toNat ≤ 15 → (W.getReg i).toNat < BabyBearP) ∧
      ofLimbs (bb (W.getReg 12)) (bb (W.getReg 13)) (bb (W.getReg 14)) (bb (W.getReg 15)) =
        poly4 (ofLimbs (bb y0) (bb y1) (bb y2) (bb y3)) ∧
      W.getReg 16 = (blake5 #v[x, y0, y1, y2, y3])[0] ∧ W.getReg 17 = (blake5 #v[x, y0, y1, y2, y3])[1] ∧
      (∀ i : Reg, 18 ≤ i.toNat → i.toNat ≤ 25 → W.getReg i = 0) ∧
      (∀ b : Word, b.toNat < ROM_END → W.mem b = s.mem b)) ∧
    (¬ (claimOK #v[x, y0, y1, y2, y3] #v[v0, v1, v2, v3] ∧ pathOK #v[x, y0, y1, y2, y3] root path) →
      ∃ m W, run m s = some W ∧ AtFinishError W) := by
  have get : ∀ i (h : i < 98), codeM[i]? = some codeM[i]! := fun i h => by
    rw [getElem!_pos codeM i (by omega)]; exact List.getElem?_eq_getElem (by omega)
  have getF : ∀ i (h : i < 113), codeF[i]? = some codeF[i]! := fun i h => by
    rw [getElem!_pos codeF i (by omega)]; exact List.getElem?_eq_getElem (by omega)
  -- `_start` and `init`, with the input empty
  set s0 := s.withInput [] with hs0
  obtain ⟨m0, S0, hrun0, hpc0, h20, hra0, hm0⟩ := start_run s0 hpc cStart
  have hrom0 : ∀ b : Word, b.toNat < ROM_END → S0.mem b = s.mem b := fun b hb =>
    hm0 b (by simp only [ROM_END] at hb; omega)
  obtain ⟨mI, S2, hrunI, hpc2, h2S2, hcp2, hrom2⟩ := main_init S0 codeM codeI Ai src hI hIl hAi hAir hsrc hpc0 h20 hra0
    (codeAt_of_rom cMain (by rw [hlen]; simp only [ROM_END]; decide) hrom0) hlen hb0 _ (get 12 (by decide)) dj0
    (codeAt_of_rom cInit (by rw [hIl]; simp only [ROM_END]; omega) hrom0)
    (codeAt_of_rom cMemcpy (by rw [memcpy_length]; simp only [ROM_END]; bv_omega) hrom0)
  obtain ⟨-, hlift⟩ := run_lift _ s0 S2 (run_trans hrun0 hrunI) rfl
  have hrunP := hlift s.input
  rw [show s0.withInput s.input = s from rfl] at hrunP
  set R := S2.withInput s.input with hR
  have hromR : ∀ b : Word, b.toNat < ROM_END → R.mem b = s.mem b := fun b hb => by
    rw [hR, withInput_mem, hrom2 b hb, hrom0 b hb]
  -- the input reads
  obtain ⟨R', hrunR, hpcR', hmR', hinR', h20R, h21R, h22R, h23R, h24R, hregR⟩ :=
    main_reads R codeM x y0 y1 y2 y3 (v0 :: v1 :: v2 :: v3 :: (pathInput root path ++ rest))
    (by rw [hR, withInput_pc, hpc2]) (codeAt_of_rom cMain (by rw [hlen]; simp only [ROM_END]; decide) hromR) hlen hbR
    (by rw [hR, withInput_input, hin])
  have hromR' : ∀ b : Word, b.toNat < ROM_END → R'.mem b = s.mem b := fun b hb => by rw [hmR', hromR b hb]
  -- `main`, parts A and B, with the input empty
  set Rq := R'.withInput [] with hRq
  have hromRq : ∀ b : Word, b.toNat < ROM_END → Rq.mem b = s.mem b := fun b hb => by rw [hRq, withInput_mem]; exact hromR' b hb
  obtain ⟨mA, T, hrunA, hpcT, h2T, h9T, hpT, hpT', hcsT, htabT, hhiT, hromT⟩ :=
    main_a S0 Rq codeM Ac Ap src x hAc hAc4 hAp hAp4 hApr hsrc (by rw [hRq, withInput_pc, hpcR'])
      (by rw [hRq, withInput_getReg, hregR _ (by decide) (by decide) (by decide) (by decide) (by decide), hR,
        withInput_getReg, h2S2]) (by rw [hRq, withInput_getReg, h20R])
      (codeAt_of_rom cMain (by rw [hlen]; simp only [ROM_END]; decide) hromRq) hlen hb1 hb2
      _ _ (get 19 (by decide)) (get 25 (by decide)) dj1 dj2
      (codeAt_of_rom cComb (by simp only [Code.combine, List.length_cons, List.length_nil, ROM_END]; bv_omega) hromRq)
      (codeAt_of_rom cInc (by simp only [Code.inc, List.length_cons, List.length_nil, ROM_END]; bv_omega) hromRq)
      (codeAt_of_rom cDbl (by simp only [Code.double, List.length_cons, List.length_nil, ROM_END]; bv_omega) hromRq)
      (codeAt_of_rom cPoly (by simp only [ROM_END]; omega) hromRq)
      (codeAt_of_rom cMul (by simp only [Code.mul_mod, List.length_cons, List.length_nil, ROM_END]; bv_omega) hromRq)
      (codeAt_of_rom cAdd (by simp only [Code.add_mod, List.length_cons, List.length_nil, ROM_END]; bv_omega) hromRq)
      (codeAt_of_rom cCoef (by rw [coeffs_length]; simp only [ROM_END]; omega) hrom0)
      (codeAt_of_rom cCoef4 (by rw [coeffs4_length]; simp only [ROM_END]; bv_omega) hrom0)
      (fun a ha => by rw [hRq, withInput_mem, hmR', hR, withInput_mem, hcp2 a ha]) hxP
  have hromT' : ∀ b : Word, b.toNat < ROM_END → T.mem b = s.mem b := fun b hb => (hromT b hb).trans (hromRq b hb)
  have kT : ∀ r : Reg, r = 20#5 ∨ r = 21#5 ∨ r = 22#5 ∨ r = 23#5 ∨ r = 24#5 → T.getReg r = R'.getReg r := fun r hr => by
    rw [hcsT r (by rcases hr with rfl|rfl|rfl|rfl|rfl <;> rv_callee_saved) (by rcases hr with rfl|rfl|rfl|rfl|rfl <;> decide),
      hRq, withInput_getReg]
  obtain ⟨mB, U, hrunB, hpcU, h2U, h9U, h18U, h19U, hcanU, hvalU, hblU, hcoU, hromU⟩ :=
    main_b T codeM codeB Aep Ab codeEP calleesEP FEP hEP hEPr hEP4 hFEP hcalr hBl hAbr (3#32 * x + 1#32) (T.getReg 10#5)
      x y0 y1 y2 y3 hpcT h2T h9T rfl ((kT _ (by decide)).trans h20R) ((kT _ (by decide)).trans h21R)
      ((kT _ (by decide)).trans h22R) ((kT _ (by decide)).trans h23R) ((kT _ (by decide)).trans h24R) htabT
      (fun a h1 h2 => by
        rw [hhiT a (by omega), hRq, withInput_mem, hmR', hR, withInput_mem, hcp2 a (by omega),
          blockCopy_outside _ _ _ _ _ (by bv_omega), hm0 a (by right; omega)]
        exact hram a (by simp only [ROM_END]; omega) (by simp only [RAM_END]; omega))
      (codeAt_of_rom cMain (by rw [hlen]; simp only [ROM_END]; decide) hromT') hlen hb3
      _ (get 33 (by decide)) dj3
      (codeAt_of_rom cEP (by simp only [ROM_END]; omega) hromT')
      (fun c hc => codeAt_of_rom (cCal c hc) (by have := hcalr c hc; simp only [ROM_END]; omega) hromT')
      (codeAt_of_rom cBl (by simp only [ROM_END]; omega) hromT') hy0p hy1p hy2p hy3p
  have hromU' : ∀ b : Word, b.toNat < ROM_END → U.mem b = s.mem b := fun b hb => (hromU b hb).trans (hromT' b hb)
  obtain ⟨-, hliftAB⟩ := run_lift _ Rq U (run_trans hrunA hrunB) rfl
  have hrunAB := hliftAB R'.input
  rw [show Rq.withInput R'.input = R' from rfl] at hrunAB
  set U1 := U.withInput R'.input with hU1
  -- the claim reads
  obtain ⟨U2, hrunV, hpcU2, hmU2, hinU2, h10U2, h11U2, h12U2, h13U2, hregU2⟩ := main_reads_v U1 codeM v0 v1 v2 v3 (pathInput root path ++ rest)
    (by rw [hU1, withInput_pc, hpcU]) (codeAt_of_rom cMain (by rw [hlen]; simp only [ROM_END]; decide)
      (fun b hb => by rw [hU1, withInput_mem]; exact hromU' b hb)) hlen hbV (by rw [hU1, withInput_input, hinR'])
  have hromU2 : ∀ b : Word, b.toNat < ROM_END → U2.mem b = s.mem b := fun b hb => by
    rw [hmU2, hU1, withInput_mem]; exact hromU' b hb
  have rU2 : ∀ r : Reg, r ≠ 10#5 → r ≠ 11#5 → r ≠ 12#5 → r ≠ 13#5 → U2.getReg r = U.getReg r := fun r a b c d => by
    rw [hregU2 r a b c d, hU1, withInput_getReg]
  have mU2 : U2.mem = U.mem := by rw [hmU2, hU1, withInput_mem]
  -- `fs_check` (with the input empty, then lifted: it reads none)
  set U2q := U2.withInput [] with hU2q
  have hromU2q : ∀ b : Word, b.toNat < ROM_END → U2q.mem b = s.mem b := fun b hb => by
    rw [hU2q, withInput_mem]; exact hromU2 b hb
  obtain ⟨mF, W1q, hrunFq, hokF, hbadF⟩ := main_f U2q codeM codeF codeEP calleesEP FEP Afs Aep Aerr hEP hEPr hEP4 hFEP
    hcalr hAfs (by simp only [ROM_END]; omega) hlenF hbFA hbFB _ (getF 53 (by decide)) djF53 _ (getF 112 (by decide))
    djF112 hAerr (by simp only [ROM_END]; omega) v0 v1 v2 v3 (by rw [hU2q, withInput_pc]; exact hpcU2)
    (by rw [hU2q, withInput_getReg, rU2 _ (by decide) (by decide) (by decide) (by decide), h2U])
    (by rw [hU2q, withInput_getReg, rU2 _ (by decide) (by decide) (by decide) (by decide), h19U])
    (by rw [hU2q, withInput_getReg]; exact h10U2) (by rw [hU2q, withInput_getReg]; exact h11U2)
    (by rw [hU2q, withInput_getReg]; exact h12U2) (by rw [hU2q, withInput_getReg]; exact h13U2)
    (fun i hi => by rw [hU2q, withInput_mem, mU2]; exact hcoU i hi)
    (codeAt_of_rom cMain (by rw [hlen]; simp only [ROM_END]; decide) hromU2q) hlen hbF _ (get 79 (by decide)) djf
    (codeAt_of_rom cFs (by rw [hlenF]; simp only [ROM_END]; omega) hromU2q)
    (codeAt_of_rom cEP (by simp only [ROM_END]; omega) hromU2q)
    (fun c hc => codeAt_of_rom (cCal c hc) (by have := hcalr c hc; simp only [ROM_END]; omega) hromU2q)
    (codeAt_of_rom cErr (by rw [show Code.finish_error.length = 6 by decide +kernel]; simp only [ROM_END]; omega)
      hromU2q)
  obtain ⟨-, liftF⟩ := run_lift _ U2q W1q hrunFq rfl
  have hrunF := liftF U2.input
  rw [show U2q.withInput U2.input = U2 from rfl] at hrunF
  set W1 := W1q.withInput U2.input with hW1
  -- the claim `fs_check` checks is `claimOK`
  have hch : limbsAt U2q.mem 0x1401000#32 = challenge (blake5 #v[x, y0, y1, y2, y3]) := by
    rw [hU2q, withInput_mem, mU2, ← hblU]; simp [limbsAt, challenge, wordsAt]
  have hclaim : claimOK #v[x, y0, y1, y2, y3] #v[v0, v1, v2, v3] ↔
      ofLimbs (v0.toNat : F) (v1.toNat : F) (v2.toNat : F) (v3.toNat : F) = poly4 (limbsAt U2q.mem 0x1401000#32) := by
    rw [hch]; rfl
  have hrunW1 := run_trans (run_trans (run_trans (run_trans hrunP hrunR) hrunAB) hrunV) hrunF
  by_cases hc : claimOK #v[x, y0, y1, y2, y3] #v[v0, v1, v2, v3]
  swap
  · refine ⟨fun h => absurd h.1 hc, fun _ => ⟨_, W1, hrunW1, ?_⟩⟩
    exact hbadF (fun h => hc (hclaim.mpr h))
  obtain ⟨hpcW1q, hcsW1q, hmW1q, hromW1q⟩ := hokF (hclaim.mp hc)
  have hpcW1 : W1.pc = 0x178#32 := by rw [hW1, withInput_pc, hpcW1q]
  have hromW1 : ∀ b : Word, b.toNat < ROM_END → W1.mem b = U2.mem b := fun b hb => by
    rw [hW1, withInput_mem, hromW1q b hb, hU2q, withInput_mem]
  have hcsW1 : ∀ i, calleeSaved i → W1.getReg i = U2.getReg i := fun i hi => by
    rw [hW1, withInput_getReg, hcsW1q i hi, hU2q, withInput_getReg]
  have hmW1 : ∀ a : Word, 0x13fff80 ≤ a.toNat → (a.toNat < 0x13fff98 ∨ 0x13fffa8 ≤ a.toNat) → W1.mem a = U2.mem a :=
    fun a h1 h2 => by rw [hW1, withInput_mem, hmW1q a h1 h2, hU2q, withInput_mem]
  have hromW1' : ∀ b : Word, b.toNat < ROM_END → W1.mem b = s.mem b := fun b hb => (hromW1 b hb).trans (hromU2 b hb)
  have csW1 : ∀ r : Reg, calleeSaved r → W1.getReg r = U.getReg r := fun r hr => by
    rw [hcsW1 r hr, rU2 r (by rintro rfl; simp [calleeSaved] at hr) (by rintro rfl; simp [calleeSaved] at hr)
      (by rintro rfl; simp [calleeSaved] at hr) (by rintro rfl; simp [calleeSaved] at hr)]
  have mW1 : ∀ a : Word, 0x13fff80 ≤ a.toNat → (a.toNat < 0x13fff98 ∨ 0x13fffa8 ≤ a.toNat) → W1.mem a = U.mem a :=
    fun a h1 h2 => by rw [hmW1 a h1 h2, mU2]
  -- the Merkle path (from the digest at `BLAKE`)
  have hleaf : readWords W1.mem 0x1401000#32 8 = blake5 #v[x, y0, y1, y2, y3] := by
    rw [← hblU]; apply Vector.ext; intro i hi
    simp only [readWords, wordsAt, Vector.getElem_ofFn]
    exact read_congr _ _ _ _ (fun j hj => mW1 _ (by bv_omega) (by right; bv_omega))
  obtain ⟨mM, W2, hrunM, hokM, hbadM⟩ := main_m W1 codeM Am codeS calleesS FS al len hS root path rest hAm hAmr hSr
    hcalrS hMal hlen256 hlen32 hFS hFS16 hpcW1 ((csW1 _ (by rv_callee_saved)).trans h2U)
    ((csW1 _ (by rv_callee_saved)).trans h19U)
    (codeAt_of_rom cMain (by rw [hlen]; simp only [ROM_END]; decide) hromW1') hlen hbM _ (get 81 (by decide)) djm
    (codeAt_of_rom cMc (by rw [show Code.merkle_check.length = 111 from rfl]; simp only [ROM_END] at hAmr ⊢; omega)
      hromW1')
    (codeAt_of_rom cMe (by rw [show Code.finish_error.length = 6 by decide +kernel]; simp only [ROM_END] at hAmr ⊢; bv_omega) hromW1')
    (codeAt_of_rom cS hSr hromW1') (fun c hc' => codeAt_of_rom (cCalS c hc') (hcalrS c hc') hromW1')
    (by rw [hW1, withInput_input, hinU2]) hd
  rw [hleaf] at hokM hbadM
  have hrunW2 := run_trans hrunW1 hrunM
  by_cases hp : pathOK #v[x, y0, y1, y2, y3] root path
  swap
  · exact ⟨fun h => absurd h.2 hp, fun _ => ⟨_, W2, hrunW2, hbadM hp⟩⟩
  refine ⟨fun _ => ?_, fun h => absurd ⟨hc, hp⟩ h⟩
  obtain ⟨hpcW2, hcsW2, -, hmW2, hromW2⟩ := hokM hp
  have hromW2' : ∀ b : Word, b.toNat < ROM_END → W2.mem b = s.mem b := fun b hb => (hromW2 b hb).trans (hromW1' b hb)
  have csW2 : ∀ r : Reg, calleeSaved r → W2.getReg r = U.getReg r := fun r hr => (hcsW2 r hr).trans (csW1 r hr)
  have mW2 : ∀ a : Word, 0x13fff80 ≤ a.toNat → (a.toNat < 0x13fff98 ∨ 0x13fffa8 ≤ a.toNat) → a.toNat < 0x1401100 →
      W2.mem a = U.mem a := fun a h1 h2 h3 => by
    rw [hmW2 a h1 (by left; rw [show MERKLE.toNat = 0x1401100 from rfl]; exact h3), mW1 a h1 h2]
  -- `main`, part C and the end
  have lf : Code.finish_success.length = 30 := by decide +kernel
  have le : Code.finish_success_extended.length = 33 := by decide +kernel
  simp only [canon4] at hcanU
  have re : ∀ (a : Word), 0x13fff88 ≤ a.toNat → a.toNat + 4 ≤ 0x13fff98 → read W2.mem a 4 = read U.mem a 4 :=
    fun a h1 h2 => read_congr _ _ _ _ (fun j hj => mW2 _ (by bv_omega) (by left; bv_omega) (by bv_omega))
  have rd : ∀ (a : Word), 0x1401000 ≤ a.toNat → a.toNat + 4 ≤ 0x1401010 → read W2.mem a 4 = read U.mem a 4 :=
    fun a h1 h2 => read_congr _ _ _ _ (fun j hj => mW2 _ (by bv_omega) (by right; bv_omega) (by bv_omega))
  obtain ⟨mC, W, hrunC, hpcW, r10, r11, r12, r13, r14, r15, r16, r17, rz, hromW⟩ :=
    main_c W2 codeM Af _ _ _ _ _ _ _ _ hAf hAfr hpcW2 ((csW2 _ (by rv_callee_saved)).trans h2U)
      ((csW2 _ (by rv_callee_saved)).trans h9U) ((csW2 _ (by rv_callee_saved)).trans h18U)
      ((csW2 _ (by rv_callee_saved)).trans h19U) (re _ (by decide) (by decide)) (re _ (by decide) (by decide))
      (re _ (by decide) (by decide)) (re _ (by decide) (by decide)) (rd _ (by decide) (by decide))
      (rd _ (by decide) (by decide))
      (codeAt_of_rom cMain (by rw [hlen]; simp only [ROM_END]; decide) hromW2') hlen hb5
      _ (get 97 (by decide)) dj5
      (codeAt_of_rom cFin (by rw [lf]; simp only [ROM_END]; omega) hromW2')
      (codeAt_of_rom cExt (by rw [le]; simp only [ROM_END]; bv_omega) hromW2')
  have hW : ∀ b : Word, b.toNat < ROM_END → W.mem b = s.mem b := fun b hb => (hromW b hb).trans (hromW2' b hb)
  refine ⟨_, W, run_trans hrunW2 hrunC, hpcW, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rz, hW⟩
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
