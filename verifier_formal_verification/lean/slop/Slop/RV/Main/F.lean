import Slop.RV.Main.B
import Slop.RV.FsCheck.Impl
import Slop.RV.Input

/-! `main`, Fiat–Shamir part (both images): the prover's claim `v` (four input reads, `csrrw a0 … a3, 0x7c0, x0`),
stored at `sp + 0x18`, and `fs_check(BLAKE, &v)`; from `main + 0x114` to `main + 0x140`. A right claim returns, a
wrong one gets the run stuck. -/

namespace RV
open _root_.RV.Sym Spec
set_option maxHeartbeats 0

/-- The four claim reads (`csrrw a0/a1/a2/a3, 0x7c0, x0`), from `main + 0x114`. -/
theorem main_reads_v (R : State) (codeM : List Word) (v0 v1 v2 v3 : Word) (rest : List Word)
    (hpc : R.pc = 0x14c#32) (hmain : CodeAt R 0x38#32 codeM) (hlen : codeM.length = 96)
    (hb : (codeM.drop 69).take 4 = (Code.main.drop 69).take 4) (hin : R.input = v0 :: v1 :: v2 :: v3 :: rest) :
    ∃ R', run 4 R = some R' ∧ R'.pc = 0x15c#32 ∧ R'.mem = R.mem ∧ R'.input = rest ∧
      R'.getReg 10#5 = v0 ∧ R'.getReg 11#5 = v1 ∧ R'.getReg 12#5 = v2 ∧ R'.getReg 13#5 = v3 ∧
      (∀ r : Reg, r ≠ 10#5 → r ≠ 11#5 → r ≠ 12#5 → r ≠ 13#5 → R'.getReg r = R.getReg r) := by
  have hc : CodeAt R (0x38#32 + BitVec.ofNat 32 (4 * 69)) ((Code.main.drop 69).take 4) :=
    hb ▸ codeAt_take (codeAt_drop hmain 69 (by rw [hlen]; bv_omega)) 4
  rw [show (Code.main.drop 69).take 4 = [0x7c001573#32, 0x7c0015f3#32, 0x7c001673#32, 0x7c0016f3#32]
    by decide +kernel] at hc
  have w : ∀ k (h : k < 4), read R.mem (0x14c#32 + BitVec.ofNat 32 (4 * k)) 4 =
      [0x7c001573#32, 0x7c0015f3#32, 0x7c001673#32, 0x7c0016f3#32][k] := fun k h => by
    rw [← hc k (by simpa using h)]; congr 1
  set R1 := (R.setReg 10#5 v0).nextInstr.withInput (v1 :: v2 :: v3 :: rest) with hR1
  set R2 := (R1.setReg 11#5 v1).nextInstr.withInput (v2 :: v3 :: rest) with hR2
  set R3 := (R2.setReg 12#5 v2).nextInstr.withInput (v3 :: rest) with hR3
  set R4 := (R3.setReg 13#5 v3).nextInstr.withInput rest with hR4
  have p1 : R1.pc = 0x150#32 := by rw [hR1]; simp [hpc]
  have p2 : R2.pc = 0x154#32 := by rw [hR2]; simp [p1]
  have p3 : R3.pc = 0x158#32 := by rw [hR3]; simp [p2]
  have p4 : R4.pc = 0x15c#32 := by rw [hR4]; simp [p3]
  have m1 : R1.mem = R.mem := by rw [hR1]; simp
  have m2 : R2.mem = R.mem := by rw [hR2]; simp [m1]
  have m3 : R3.mem = R.mem := by rw [hR3]; simp [m2]
  have m4 : R4.mem = R.mem := by rw [hR4]; simp [m3]
  have s1 := step_read R 0x7c001573#32 .rw 10#5 v0 _ (by rw [hpc]; decide) (by rw [hpc]; decide)
    (by rw [hpc]; exact w 0 (by decide)) (by decide +kernel) hin
  have s2 := step_read R1 0x7c0015f3#32 .rw 11#5 v1 _ (by rw [p1]; decide) (by rw [p1]; decide)
    (by rw [p1, m1]; exact w 1 (by decide)) (by decide +kernel) rfl
  have s3 := step_read R2 0x7c001673#32 .rw 12#5 v2 _ (by rw [p2]; decide) (by rw [p2]; decide)
    (by rw [p2, m2]; exact w 2 (by decide)) (by decide +kernel) rfl
  have s4 := step_read R3 0x7c0016f3#32 .rw 13#5 v3 _ (by rw [p3]; decide) (by rw [p3]; decide)
    (by rw [p3, m3]; exact w 3 (by decide)) (by decide +kernel) rfl
  refine ⟨R4, by rw [run_succ, s1, Option.bind_some, ← hR1, run_succ, s2, Option.bind_some, ← hR2, run_succ, s3,
    Option.bind_some, ← hR3, run_succ, s4, Option.bind_some, ← hR4]; rfl, p4, m4, by rw [hR4, withInput_input],
    ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp only [hR4, hR3, hR2, hR1, withInput_getReg, next_r, r_set, BitVec.reduceEq, ite_true, ite_false]
  intro r a b c d
  simp only [a, b, c, d, ite_false]
  split <;> simp_all [r_zero5]

namespace MainF'
abbrev rF : Region := ⟨2, 0, 112, 16⟩
end MainF'
open MainF'

/-- From after the claim reads (`main + 0x124`): `v` stored at `sp + 0x18`, `fs_check(s3, sp + 0x18)`. -/
theorem main_f (U : State) (codeM codeF codeEP : List Word) (calleesEP : List (Word × List Word)) (FEP : Nat)
    (Afs Aep Aerr : Word)
    (hEP : ImplementsAtW Aep codeEP calleesEP FEP e4polyPre 16 e4polyPost)
    (hEPr : Aep.toNat + 4 * codeEP.length ≤ ROM_END) (hEP4 : Aep.toNat % 4 = 0) (hFEP : FEP ≤ 0x100000)
    (hcalr : ∀ c ∈ calleesEP, c.1.toNat + 4 * c.2.length ≤ ROM_END)
    (hAfs : Afs.toNat % 4 = 0) (hAfsr : Afs.toNat + 4 * 113 ≤ ROM_END) (hlenF : codeF.length = 113)
    (hbA : codeF.take 53 = Code.fs_check.take 53) (hbB : (codeF.drop 54).take 58 = (Code.fs_check.drop 54).take 58)
    (j53 : Word) (hj53 : codeF[53]? = some j53)
    (dj53 : decode j53 = some (.jal 1#5 (Aep - (Afs + BitVec.ofNat 32 (4 * 53)))))
    (j112 : Word) (hj112 : codeF[112]? = some j112)
    (dj112 : decode j112 = some (.jal 1#5 (Aerr - (Afs + BitVec.ofNat 32 (4 * 112)))))
    (hAerr : Aerr.toNat % 4 = 0) (hAerrr : Aerr.toNat + 24 ≤ ROM_END)
    (v0 v1 v2 v3 : Word)
    (hpc : U.pc = 0x15c#32) (h2 : U.getReg 2#5 = 0x13fff80#32) (h19 : U.getReg 19#5 = 0x1401000#32)
    (h10 : U.getReg 10#5 = v0) (h11 : U.getReg 11#5 = v1) (h12 : U.getReg 12#5 = v2) (h13 : U.getReg 13#5 = v3)
    (htab : CodeMem U.mem (0x1400000#32 + BitVec.ofNat 32 0x190) Code.COEFFS4)
    (hmain : CodeAt U 0x38#32 codeM) (hlen : codeM.length = 96)
    (hbF : (codeM.drop 73).take 6 = (Code.main.drop 73).take 6)
    (jf : Word) (hjf : codeM[79]? = some jf) (djf : decode jf = some (.jal 1#5 (Afs - 0x174#32)))
    (hfs : CodeAt U Afs codeF) (hEPc : CodeAt U Aep codeEP) (hcal : ∀ c ∈ calleesEP, CodeAt U c.1 c.2)
    (herr : CodeAt U Aerr Code.finish_error) :
    ∃ m W, run m U = some W ∧
      (ofLimbs (v0.toNat : F) (v1.toNat : F) (v2.toNat : F) (v3.toNat : F) = poly4 (limbsAt U.mem 0x1401000#32) →
        W.pc = 0x178#32 ∧ (∀ r : Reg, calleeSaved r → W.getReg r = U.getReg r) ∧
        (∀ a : Word, 0x13fff80 ≤ a.toNat → (a.toNat < 0x13fff98 ∨ 0x13fffa8 ≤ a.toNat) → W.mem a = U.mem a) ∧
        (∀ b : Word, b.toNat < ROM_END → W.mem b = U.mem b)) ∧
      (ofLimbs (v0.toNat : F) (v1.toNat : F) (v2.toNat : F) (v3.toNat : F) ≠ poly4 (limbsAt U.mem 0x1401000#32) →
        AtFinishError W) := by
  have hl : Code.main.length = 96 := by decide +kernel
  obtain ⟨_, e79⟩ := List.getElem?_eq_some_iff.mp hjf
  simp only [ROM_END, RAM_END] at *
  have h2n : (U.getReg 2#5).toNat = 0x13fff80 := by rw [h2]; rfl
  have eF : (0x38#32 + BitVec.ofNat 32 (4 * 73) + BitVec.ofNat 32 (4 * 6) + (Afs - 0x174#32) : Word) = Afs := by
    bv_omega
  have hc : CodeAt U (0x38#32 + BitVec.ofNat 32 (4 * 73)) ((Code.main.drop 73).take 6) :=
    hbF ▸ codeAt_take (codeAt_drop hmain 73 (by rw [hlen]; bv_omega)) 6
  obtain ⟨T0, hrun0, hrel0, hrom0, hout0, hfr0⟩ := block_jal _ MainF.instrs MainF.σ U _ (Afs - 0x174#32) [rF] []
    MainF.dec MainF.run (by rw [hpc]; decide) (by decide) (by simp [hl, ROM_END]) hc jf
    (by
      rw [show ((Code.main.drop 73).take 6).length = 6 by decide +kernel,
        show (0x38#32 + BitVec.ofNat 32 (4 * 73) + BitVec.ofNat 32 (4 * 6) : Word) =
          0x38#32 + BitVec.ofNat 32 (4 * 79) by decide]
      exact (hmain 79 (by omega)).trans e79)
    djf (by rw [show ((Code.main.drop 73).take 6).length = 6 by decide +kernel, eF]; exact hAfs) (by sym_side)
    (by simp) (by decide +kernel)
  simp only [List.length_take, List.length_drop, hl, show min 6 (96 - 73) = 6 from rfl] at hrun0
  set S := (T0.setPC (0x38#32 + BitVec.ofNat 32 (4 * 73) + BitVec.ofNat 32 (4 * 6) + (Afs - 0x174#32))).setReg 1#5
    (0x38#32 + BitVec.ofNat 32 (4 * 73) + BitVec.ofNat 32 (4 * 6) + 4) with hS
  have j : ∀ r : Reg, r ≠ 1#5 → S.getReg r = T0.getReg r := fun r hr => by rw [hS, jal_getReg _ _ _ _ hr]
  have hpcS : S.pc = Afs := by rw [hS, jal_pc]; bv_omega
  have hraS : S.getReg 1#5 = 0x178#32 := by rw [hS, jal_getReg1]; rfl
  have sromS : ∀ b : Word, b.toNat < 4194304 → S.mem b = U.mem b := fun b hb => by
    rw [hS, jal_mem]; exact hrom0 b (by simp only [ROM_END]; omega)
  have spS : S.getReg 2#5 = 0x13fff80#32 := by rw [j _ (by decide), hrel0.reg_same _ MainF.run _ (by decide +kernel), h2]
  have a0S : S.getReg 10#5 = 0x1401000#32 := by
    rw [j _ (by decide), hrel0.reg_var _ MainF.run 10#5 19 (by decide) (by decide +kernel),
      show (BitVec.ofNat 5 19 : Reg) = 19#5 from rfl, h19]
  have a1S : S.getReg 11#5 = 0x13fff98#32 := by
    rw [j _ (by decide), hrel0.reg_addr _ MainF.run 11#5 2 24#32 (by decide) (by decide +kernel) (by decide +kernel),
      show (BitVec.ofNat 5 2 : Reg) = 2#5 from rfl, h2]; rfl
  have csS : ∀ r : Reg, calleeSaved r → S.getReg r = U.getReg r := fun r hr => by
    rw [j r (by rintro rfl; simp [calleeSaved] at hr)]
    rcases calleeSaved_cases r hr with h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst h <;>
      exact hrel0.reg_same _ MainF.run _ (by decide +kernel)
  -- `v` stored at `sp + 24`; memory else unchanged
  have st : ∀ (k : Word) (i : Nat) (v : Word), outOK MainF.σ [rF] [] 2 k = true → outNode MainF.σ 2 k = i →
      i < 32 → U.getReg (BitVec.ofNat 5 i) = v → read S.mem (0x13fff80#32 + k) 4 = v := fun k i v h hn hi hv => by
    rw [hS, jal_mem, ← h2, ← hv, ← val_init _ _ MainF.run U i hi, ← hn]; exact hout0 2 k (by decide) h
  have sv0 := st 24#32 10 v0 (by decide +kernel) (by decide +kernel) (by decide) h10
  have sv1 := st 28#32 11 v1 (by decide +kernel) (by decide +kernel) (by decide) h11
  have sv2 := st 32#32 12 v2 (by decide +kernel) (by decide +kernel) (by decide) h12
  have sv3 := st 36#32 13 v3 (by decide +kernel) (by decide +kernel) (by decide) h13
  simp only [BitVec.reduceAdd] at sv0 sv1 sv2 sv3
  have sout : ∀ a : Word, (a.toNat < 0x13fff98 ∨ 0x13fffa8 ≤ a.toNat) → S.mem a = U.mem a := fun a ha => by
    rw [hS, jal_mem]
    apply hfr0 [⟨2, 24, 40, 1⟩] (by decide +kernel) (by sym_side) a
    intro R hR; simp only [List.mem_singleton] at hR; subst hR
    simp only [Region.Outside, show (BitVec.ofNat 5 2 : Reg) = 2#5 from rfl, h2n]; omega
  -- `fs_check`
  obtain ⟨m2, W, hrun2, hok, hbad⟩ := fs_check_run Afs Aep Aerr codeF codeEP calleesEP FEP hEP hEPr hEP4 hFEP hcalr
    S hpcS hAfs hAfsr (codeAt_of_rom hfs (by rw [hlenF]; simp only [ROM_END]; omega) sromS) hlenF hbA hbB j53 hj53
    dj53 j112 hj112 dj112 (codeAt_of_rom hEPc (by simp only [ROM_END]; omega) sromS)
    (fun c hc => codeAt_of_rom (hcal c hc) (by have := hcalr c hc; simp only [ROM_END]; omega) sromS)
    (codeAt_of_rom herr (by rw [show Code.finish_error.length = 6 by decide +kernel]; simp only [ROM_END]; omega)
      sromS) hAerr hAerrr (by rw [spS]; decide) (by rw [spS]; simp only [ROM_END, BitVec.toNat_ofNat]; omega)
    (by rw [spS]; decide)
    (by rw [hraS]; decide) (by simp only [argOk, spS, a0S, RAM_END]; decide)
    (by simp only [argOk, spS, a1S, RAM_END]; decide)
    (fun i hi => by
      rw [read_congr S.mem U.mem _ 4 (fun j hj => sout _ (by right; rw [coeffs4_length] at hi; bv_omega))]
      exact htab i hi)
  -- the claim `fs_check` checks
  have hclaim : fsClaim S.mem (S.getReg 10#5) (S.getReg 11#5) ↔
      ofLimbs (v0.toNat : F) (v1.toNat : F) (v2.toNat : F) (v3.toNat : F) = poly4 (limbsAt U.mem 0x1401000#32) := by
    have hd : limbsAt S.mem 0x1401000#32 = limbsAt U.mem 0x1401000#32 := by
      simp only [limbsAt]
      rw [read_congr S.mem U.mem _ 4 (fun j hj => sout _ (by right; bv_omega)),
        read_congr S.mem U.mem _ 4 (fun j hj => sout _ (by right; bv_omega)),
        read_congr S.mem U.mem _ 4 (fun j hj => sout _ (by right; bv_omega)),
        read_congr S.mem U.mem _ 4 (fun j hj => sout _ (by right; bv_omega))]
    simp only [fsClaim, a0S, a1S, hd]
    simp only [limbsAt, BitVec.reduceAdd, sv0, sv1, sv2, sv3]
  refine ⟨_, W, run_trans hrun0 hrun2, fun hc => ?_, fun hc => hbad (fun h => hc (hclaim.mp h))⟩
  obtain ⟨t1, t2, t3⟩ := hok (hclaim.mpr hc)
  refine ⟨by rw [t1, hraS], fun r hr => (t2 r hr).trans (csS r hr), fun a h1 h2' => ?_, fun b hb => ?_⟩
  · rw [t3 a (by right; rw [spS]; exact h1), sout a h2']
  · rw [t3 b (by left; rw [spS]; simp only [BitVec.toNat_ofNat]; omega), sromS b (by omega)]

end RV
