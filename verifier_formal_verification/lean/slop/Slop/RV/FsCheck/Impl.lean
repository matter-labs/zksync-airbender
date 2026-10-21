import Slop.RV.FsCheck.PartA
import Slop.RV.FsCheck.PartB
import Slop.RV.FsCheck.Inj
import Slop.RV.Coeffs4

/-! `fs_check(st, v)`: part A, `ext4_poly` (any implementation of its contract), part B. If the claim `v` is `poly4`
of the challenge from `st`, it returns like a function; otherwise the run gets stuck. -/

namespace RV
open _root_.RV.Sym Spec
set_option maxHeartbeats 400000

/-- `fs_check`'s claim: the 4 words at `v` are `poly4` of the challenge, the 4 words at `st` (as BabyBear elements:
`limbsAt` casts each word to the field, i.e. reduces it). -/
def fsClaim (m : Word → BitVec 8) (st v : Word) : Prop := limbsAt m v = poly4 (limbsAt m st)

theorem limbsAt_red (m m' : Word → BitVec 8) (p q : Word)
    (h0 : read m' q 4 = red (read m p 4)) (h1 : read m' (q + 4#32) 4 = red (read m (p + 4#32) 4))
    (h2 : read m' (q + 8#32) 4 = red (read m (p + 8#32) 4)) (h3 : read m' (q + 12#32) 4 = red (read m (p + 12#32) 4)) :
    limbsAt m' q = limbsAt m p := by
  simp only [limbsAt, h0, h1, h2, h3, red_bb]

theorem word_of_cast {a b : Word} (ha : a.toNat < BabyBearP) (hb : b.toNat < BabyBearP)
    (h : (a.toNat : F) = (b.toNat : F)) : a = b := by
  rw [ZMod.natCast_eq_natCast_iff'] at h
  rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h
  exact BitVec.eq_of_toNat_eq h

/-- The comparison `fs_check` makes is the claim. -/
theorem limbsMatch_iff (m m' : Word → BitVec 8) (out v st : Word) (hc : canon4 m' out)
    (hv : ∀ k : Word, k.toNat ≤ 12 → read m' (v + k) 4 = read m (v + k) 4)
    (he : limbsAt m' out = poly4 (limbsAt m st)) :
    limbsMatch m' out v ↔ fsClaim m st v := by
  have hv0 := hv 0#32 (by decide); rw [BitVec.add_zero] at hv0
  have hv1 := hv 4#32 (by decide); have hv2 := hv 8#32 (by decide); have hv3 := hv 12#32 (by decide)
  constructor
  · intro hm
    obtain ⟨m0, m1, m2, m3⟩ := hm
    unfold fsClaim; rw [← he]
    simp only [limbsAt, m0, m1, m2, m3, red_bb, hv0, hv1, hv2, hv3]
  · intro hcl
    unfold fsClaim at hcl
    rw [← he] at hcl
    simp only [limbsAt] at hcl
    obtain ⟨e0, e1, e2, e3⟩ := ofLimbs_inj hcl
    obtain ⟨c0, c1, c2, c3⟩ := hc
    refine ⟨?_, ?_, ?_, ?_⟩ <;> apply word_of_cast (by assumption) (red_lt _) <;> rw [red_bb] <;>
      simp only [hv0, hv1, hv2, hv3] <;> first | exact e0.symm | exact e1.symm | exact e2.symm | exact e3.symm

/-- `fs_check` at `A` (its words `codeF`; `ext4_poly` at `Aep` with any implementation of its contract,
`zksync_os_finish_error` at `Aerr`), called with `st = a0`, `v = a1` (16 bytes each, above `sp`): with a right claim
it returns (callee-saved registers restored, memory changed only in its frames); with a wrong one the run gets
stuck. -/
theorem fs_check_run (A Aep Aerr : Word) (codeF codeEP : List Word) (calleesEP : List (Word × List Word)) (FEP : Nat)
    (hEP : ImplementsAtW Aep codeEP calleesEP FEP e4polyPre 16 e4polyPost)
    (hEPr : Aep.toNat + 4 * codeEP.length ≤ ROM_END) (hEP4 : Aep.toNat % 4 = 0) (hFEP : FEP ≤ 0x100000)
    (hcalr : ∀ c ∈ calleesEP, c.1.toNat + 4 * c.2.length ≤ ROM_END)
    (s : State) (hpc : s.pc = A) (hal : A.toNat % 4 = 0) (hrom : A.toNat + 4 * 113 ≤ ROM_END)
    (hcode : CodeAt s A codeF) (hlen : codeF.length = 113)
    (hbA : codeF.take 53 = Code.fs_check.take 53) (hbB : (codeF.drop 54).take 58 = (Code.fs_check.drop 54).take 58)
    (j53 : Word) (hj53 : codeF[53]? = some j53) (dj53 : decode j53 = some (.jal 1#5 (Aep - (A + BitVec.ofNat 32 (4 * 53)))))
    (j112 : Word) (hj112 : codeF[112]? = some j112)
    (dj112 : decode j112 = some (.jal 1#5 (Aerr - (A + BitVec.ofNat 32 (4 * 112)))))
    (hEPc : CodeAt s Aep codeEP) (hcal : ∀ c ∈ calleesEP, CodeAt s c.1 c.2)
    (herr : CodeAt s Aerr Code.finish_error) (hAerr : Aerr.toNat % 4 = 0) (hAerrr : Aerr.toNat + 24 ≤ ROM_END)
    (hsp16 : (s.getReg 2#5).toNat % 16 = 0) (hspl : ROM_END + 80 + FEP ≤ (s.getReg 2#5).toNat)
    (hsph : (s.getReg 2#5).toNat ≤ 0x1400190) (hra : (s.getReg 1#5).toNat % 4 = 0)
    (hst : argOk (s.getReg 2#5) (s.getReg 10#5)) (hv : argOk (s.getReg 2#5) (s.getReg 11#5))
    (htab : CodeMem s.mem 0x1400190#32 Code.COEFFS4) :
    ∃ m T, run m s = some T ∧
      (fsClaim s.mem (s.getReg 10#5) (s.getReg 11#5) →
        T.pc = s.getReg 1#5 ∧ (∀ i, calleeSaved i → T.getReg i = s.getReg i) ∧
        (∀ a : Word, a.toNat + (64 + FEP) < (s.getReg 2#5).toNat ∨ (s.getReg 2#5).toNat ≤ a.toNat →
          T.mem a = s.mem a)) ∧
      (¬ fsClaim s.mem (s.getReg 10#5) (s.getReg 11#5) → AtFinishError T) := by
  have hst' := hst; have hv' := hv
  obtain ⟨hst4, hsts, hstr⟩ := hst
  obtain ⟨hv4, hvs, hvr⟩ := hv
  simp only [ROM_END, RAM_END] at *
  have eA : A + BitVec.ofNat 32 (4 * 53) + (Aep - (A + BitVec.ofNat 32 (4 * 53))) = Aep := by bv_omega
  have htgt : (A + BitVec.ofNat 32 (4 * 53) + (Aep - (A + BitVec.ofNat 32 (4 * 53)))).toNat % 4 = 0 := by
    rw [eA]; exact hEP4
  have hLe : Code.finish_error.length = 6 := by decide +kernel
  -- part A
  obtain ⟨S1, hrun1, hpc1, r1, r2, r10, r11, r9, r8, r18, r19, r20, hrom1, hfr1, z0, z1, z2, z3, k1, k8, k9, k18,
    k19⟩ := fs_part_a A (Aep - (A + BitVec.ofNat 32 (4 * 53))) s codeF hpc hal (by simp only [ROM_END]; omega) hcode
      (by omega) hbA j53 hj53 dj53 htgt hsp16 (by simp only [ROM_END]; omega) (by simp only [RAM_END]; omega) hst'
  have hpc1' : S1.pc = Aep := by rw [hpc1, eA]
  have s1rom : ∀ b : Word, b.toNat < 4194304 → S1.mem b = s.mem b := fun b hb => hrom1 b (by simp only [ROM_END]; omega)
  have hsp1 : (S1.getReg 2#5).toNat = (s.getReg 2#5).toNat - 64 := by rw [r2]; bv_omega
  -- `ext4_poly(sp - 40, sp - 56)`
  obtain ⟨n2, S2, hrun2, hpc2, hpost2, hcs2, hmem2⟩ := hEP S1 hpc1'
    (fun c hc => codeAt_of_rom (hcal c hc) (by have := hcalr c hc; simp only [ROM_END]; omega) s1rom)
    ⟨(by rw [hpc1']; exact codeAt_of_rom hEPc (by simp only [ROM_END]; omega) s1rom),
      (by rw [hpc1']; exact hEP4), (by rw [hpc1']; simp only [ROM_END]; omega),
      (by show (S1.getReg 1#5).toNat % 4 = 0; rw [r1]; bv_omega),
      (by show (S1.getReg 2#5).toNat % 16 = 0; rw [r2]; bv_omega),
      (by show ROM_END + FEP ≤ (S1.getReg 2#5).toNat; rw [hsp1]; simp only [ROM_END]; omega),
      (by show (S1.getReg 2#5).toNat ≤ RAM_END; rw [hsp1]; simp only [RAM_END]; omega)⟩
    (by
      simp only [e4polyPre, argOk, RAM_END, r2, r10, r11, canon4]
      refine ⟨⟨by bv_omega, by bv_omega, by bv_omega⟩, ⟨by bv_omega, by bv_omega, by bv_omega⟩, ?_, fun i hi => ?_,
        by bv_omega⟩
      · rw [z0, show s.getReg 2#5 + 4294967240#32 + 4#32 = s.getReg 2#5 + 4294967244#32 by bv_omega, z1]
        rw [show s.getReg 2#5 + 4294967240#32 + 8#32 = s.getReg 2#5 + 4294967248#32 by bv_omega, z2]
        rw [show s.getReg 2#5 + 4294967240#32 + 12#32 = s.getReg 2#5 + 4294967252#32 by bv_omega, z3]
        exact ⟨red_lt _, red_lt _, red_lt _, red_lt _⟩
      · rw [read_congr _ s.mem _ 4 (fun j hj => hfr1 _ (by right; rw [coeffs4_length] at hi; bv_omega))]
        exact htab i hi)
  replace hpc2 : S2.pc = S1.getReg 1#5 := hpc2
  replace hcs2 : ∀ i, calleeSaved i → S2.getReg i = S1.getReg i := hcs2
  replace hmem2 : ∀ a : Word, a.toNat + FEP < (S1.getReg 2#5).toNat ∨ (S1.getReg 2#5).toNat ≤ a.toNat →
      a.toNat < (S1.getReg 10#5).toNat ∨ (S1.getReg 10#5).toNat + 16 ≤ a.toNat → S2.mem a = S1.mem a := hmem2
  rw [hsp1, r10] at hmem2
  simp only [e4polyPost, r10, r11] at hpost2
  obtain ⟨hcanE, hvalE⟩ := hpost2
  have s2rom : ∀ b : Word, b.toNat < 4194304 → S2.mem b = s.mem b := fun b hb => by
    rw [hmem2 b (by left; omega) (by left; bv_omega), s1rom b hb]
  -- above `sp - 40 + 16`: as at the call of `fs_check`, or as part A left it
  have s2hi : ∀ a : Word, (s.getReg 2#5).toNat - 24 ≤ a.toNat → S2.mem a = S1.mem a := fun a ha =>
    hmem2 a (by right; omega) (by right; bv_omega)
  have kk : ∀ (k : Word) (v : Word), (s.getReg 2#5 + k).toNat + 4 ≤ (s.getReg 2#5).toNat →
      (s.getReg 2#5).toNat - 24 ≤ (s.getReg 2#5 + k).toNat → read S1.mem (s.getReg 2#5 + k) 4 = v →
      read S2.mem (s.getReg 2#5 + k) 4 = v := fun k v h1 h2' h => by
    rw [← h]; exact read_congr _ _ _ _ (fun j hj => s2hi _ (by bv_omega))
  -- part B
  obtain ⟨m3, T, hrun3, hok, hbad⟩ := fs_part_b A Aerr s S2 codeF hal (by simp only [ROM_END]; omega)
    (by rw [hpc2, r1]; bv_omega) (codeAt_of_rom hcode (by rw [hlen]; simp only [ROM_END]; omega) s2rom) hlen hbB j112
    hj112 dj112 (codeAt_of_rom herr (by rw [hLe]; simp only [ROM_END]; omega) s2rom) hAerr (by simp only [ROM_END]; omega) hsp16 (by simp only [ROM_END]; omega)
    (by simp only [RAM_END]; omega) hv' hra
    (by rw [hcs2 _ (by rv_callee_saved), r2]) (by rw [hcs2 _ (by rv_callee_saved), r9])
    (by rw [hcs2 _ (by rv_callee_saved), r18]) (by rw [hcs2 _ (by rv_callee_saved), r19])
    (fun r h1 h2' => by rw [hcs2 r (by unfold calleeSaved; right; right; right; omega), r20 r h1 h2'])
    (kk _ _ (by bv_omega) (by bv_omega) k1) (kk _ _ (by bv_omega) (by bv_omega) k8)
    (kk _ _ (by bv_omega) (by bv_omega) k9) (kk _ _ (by bv_omega) (by bv_omega) k18)
    (kk _ _ (by bv_omega) (by bv_omega) k19)
  -- the comparison is the claim
  have a1 : s.getReg 2#5 + 4294967240#32 + 4#32 = s.getReg 2#5 + 4294967244#32 := by bv_omega
  have a2 : s.getReg 2#5 + 4294967240#32 + 8#32 = s.getReg 2#5 + 4294967248#32 := by bv_omega
  have a3 : s.getReg 2#5 + 4294967240#32 + 12#32 = s.getReg 2#5 + 4294967252#32 := by bv_omega
  have hz : limbsAt S1.mem (s.getReg 2#5 + 4294967240#32) = limbsAt s.mem (s.getReg 10#5) :=
    limbsAt_red _ _ _ _ z0 (by rw [a1]; exact z1) (by rw [a2]; exact z2) (by rw [a3]; exact z3)
  rw [hz] at hvalE
  have hiff := limbsMatch_iff s.mem S2.mem (s.getReg 2#5 + 4294967256#32) (s.getReg 11#5) (s.getReg 10#5) hcanE
    (fun k hk => read_congr _ _ _ _ (fun j hj => by rw [s2hi _ (by bv_omega)]; exact hfr1 _ (by right; bv_omega)))
    hvalE
  refine ⟨54 + n2 + m3, T, run_trans (run_trans hrun1 hrun2) hrun3, fun hc => ?_, fun hc => hbad (hc ∘ hiff.mp)⟩
  obtain ⟨t1, t2, t3⟩ := hok (hiff.mpr hc)
  refine ⟨t1, t2, fun a ha => ?_⟩
  rw [t3 a (by omega), hmem2 a (by omega) (by bv_omega)]
  exact hfr1 a (by omega)

end RV
