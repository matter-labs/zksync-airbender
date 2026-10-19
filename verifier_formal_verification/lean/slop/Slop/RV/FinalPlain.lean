import Slop.RV.Main.Run
import Slop.RV.InitMop
import Slop.RV.Ext4Poly.Impl
import Slop.RV.Link
import Slop.RV.Merkle.Step
import Slop.RV.Stuck

/-! The final theorem for the plain image: link check (image bytes = the code and tables the proofs use), then the
whole program (`main_run`); a wrong claim: the run gets stuck, so it never halts (`stuck_never_halts`). -/

namespace RV
open Spec

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem program_correct_run (s : State) (x y0 y1 y2 y3 v0 v1 v2 v3 : Word) (root : Vector Word 8)
    (path : List MerkleStep) (rest : List Word) (hpc : s.pc = 0)
    (himg : ImageLoaded Image.bytes s) (hram : RamZero s)
    (hin : s.input = x :: y0 :: y1 :: y2 :: y3 :: v0 :: v1 :: v2 :: v3 :: (pathInput root path ++ rest))
    (hd : path.length ≤ 32) (hxP : x.toNat ≤ P)
    (hy0p : y0.toNat < BabyBearP) (hy1p : y1.toNat < BabyBearP) (hy2p : y2.toNat < BabyBearP)
    (hy3p : y3.toNat < BabyBearP) :
    read s.mem (BitVec.ofNat 32 Image.halt) 4 = 0x0000006f#32 ∧
    (claimOK #v[x, y0, y1, y2, y3] #v[v0, v1, v2, v3] ∧ pathOK #v[x, y0, y1, y2, y3] root path →
    ∃ m W, run m s = some W ∧ W.pc = BitVec.ofNat 32 Image.halt ∧
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
  have hs : Image.bytes.size < 2 ^ 32 := by decide +kernel
  have cStart := codeAt_of_bytesW himg 0 Code.start (by decide +kernel) hs (by decide +kernel)
  have cMain := codeAt_of_bytesW himg 0x38 Code.main (by decide +kernel) hs (by decide +kernel)
  have cInit := codeAt_of_bytesW himg 0x287c Code.init (by decide +kernel) hs (by decide +kernel)
  have cMemcpy := codeAt_of_bytesW himg 0x2904 Code.memcpy (by decide +kernel) hs (by decide +kernel)
  have cComb := codeAt_of_bytesW himg 0x2648 Code.combine (by decide +kernel) hs (by decide +kernel)
  have cInc := codeAt_of_bytesW himg 0x26b4 Code.inc (by decide +kernel) hs (by decide +kernel)
  have cDbl := codeAt_of_bytesW himg 0x2690 Code.double (by decide +kernel) hs (by decide +kernel)
  have cPoly := codeAt_of_bytesW himg 0x22f0 Code.poly_eval (by decide +kernel) hs (by decide +kernel)
  have cMul := codeAt_of_bytesW himg 0x22b4 Code.mul_mod (by decide +kernel) hs (by decide +kernel)
  have cAdd := codeAt_of_bytesW himg 0x2280 Code.add_mod (by decide +kernel) hs (by decide +kernel)
  have cEP := codeAt_of_bytesW himg 0x1e8c Code.ext4_poly (by decide +kernel) hs (by decide +kernel)
  have cHor := codeAt_of_bytesW himg 0x1800 Code.ext4_horner (by decide +kernel) hs (by decide +kernel)
  have cMA := codeAt_of_bytesW himg 0x18a8 Code.ext4_mul_add (by decide +kernel) hs (by decide +kernel)
  have cBl := codeAt_of_bytesW himg 0x1c0 Code.blake2s_compress (by decide +kernel) hs (by decide +kernel)
  have cFin := codeAt_of_bytesW himg 0x2758 Code.finish_success (by decide +kernel) hs (by decide +kernel)
  have cExt := codeAt_of_bytesW himg 0x27d0 Code.finish_success_extended (by decide +kernel) hs (by decide +kernel)
  have cFs := codeAt_of_bytesW himg 0x20bc Code.fs_check (by decide +kernel) hs (by decide +kernel)
  have cErr := codeAt_of_bytesW himg 0x2740 Code.finish_error (by decide +kernel) hs (by decide +kernel)
  have cMc := codeAt_of_bytesW himg 0x236c Code.merkle_check (by decide +kernel) hs (by decide +kernel)
  have cMs := codeAt_of_bytesW himg 0x2528 Code.merkle_step (by decide +kernel) hs (by decide +kernel)
  have cCoef := codeAt_of_bytesW himg 0x4334 Code.COEFFS (by decide +kernel) hs (by decide +kernel)
  have cCoef4 := codeAt_of_bytesW himg (0x4334 + 0x190) Code.COEFFS4 (by decide +kernel) hs (by decide +kernel)
  simp only [BitVec.ofNat_eq_ofNat] at *
  have H := main_run s Code.main Code.init Code.ext4_poly Code.blake2s_compress
      [(0x1e8c#32 + 4294965620#32, Code.ext4_horner), (0x1e8c#32 + 4294965620#32 + 168#32, Code.ext4_mul_add)] 192
      Code.fs_check 0x287c#32 0x2648#32 0x22f0#32 0x1e8c#32 0x1c0#32 0x2758#32 0x20bc#32
      0x2740#32 0x4334#32 x y0 y1 y2 y3 v0 v1 v2 v3
      (init_run 0x287c#32 (by decide) (by decide)) (by decide +kernel) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide)
      (ext4_poly_impl 0x1e8c#32 (by decide) (by decide)) (by decide +kernel) (by decide) (by decide)
      (by intro c hc; simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
          rcases hc with h | h <;> subst h <;> decide +kernel)
      (main_blake Code.main 0x1c0#32 (by decide +kernel) (by decide) (by decide +kernel) rfl _ rfl (by decide +kernel))
      (by decide +kernel) (by decide) (by decide)
      (by decide) (by decide) (by decide +kernel) rfl rfl (by decide +kernel) (by decide +kernel) (by decide) (by decide)
      0x236c#32 Code.merkle_step [(0x236c#32 + 0x1bc#32 + 284#32 + 0xFFFFDB7C#32, Code.blake2s_compress)] 160 4 132
      (merkle_step_impl (0x236c#32 + 0x1bc#32) (by decide +kernel)) (by decide) (by decide) (by decide +kernel)
      (by intro c hc; simp only [List.mem_cons, List.not_mem_nil, or_false] at hc; subst hc; decide +kernel)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide +kernel) rfl rfl rfl rfl rfl rfl rfl rfl rfl
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)
      hpc cStart cMain cInit cMemcpy cComb cInc cDbl cPoly cMul cAdd cCoef cCoef4 cEP
      (by
        intro c hc; simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with h | h <;> subst h
        · exact cHor
        · exact cMA)
      cBl cFin cExt cFs cErr cMc cErr cMs
      (by intro c hc; simp only [List.mem_cons, List.not_mem_nil, or_false] at hc; subst hc; exact cBl)
      root path hd hram rest hin hxP hy0p hy1p hy2p hy3p
  have hhalt : read s.mem (BitVec.ofNat 32 Image.halt) 4 = 0x0000006f#32 := by
    have := cExt 32 (by decide)
    simpa [Code.finish_success_extended, Image.halt, BitVec.ofNat_eq_ofNat] using this
  refine ⟨hhalt, fun hc => ?_, H.2⟩
  obtain ⟨m, W, hrun, hpcW, rest'⟩ := H.1 hc
  exact ⟨m, W, hrun, by rw [hpcW]; rfl, rest'⟩

set_option maxRecDepth 100000 in
/-- Airbender's decoder accepts the image (no delegation runs of other lengths). -/
theorem accepted : Accepted Image.bytes := by decide +kernel

set_option maxHeartbeats 0 in
theorem program_correct : ProgramCorrect := by
  refine ⟨accepted, ?_⟩
  intro s x y0 y1 y2 y3 v0 v1 v2 v3 root path rest hpc himg hram hin hd hxP hy0p hy1p hy2p hy3p
  obtain ⟨hhalt, hok, hbad⟩ := program_correct_run s x y0 y1 y2 y3 v0 v1 v2 v3 root path rest hpc himg hram hin hd hxP
    hy0p hy1p hy2p hy3p
  refine ⟨fun hc => ?_, fun hc => ?_⟩
  · obtain ⟨m, W, hrun, hpcW, r10, r11, r11', r12, rl, r16, r17, rz, hromW⟩ := hok hc
    refine ⟨m, W, hrun, hpcW, r10, r11, r11', r12, rl, r16, r17, rz, ?_⟩
    refine halt_forever W (by rw [hpcW]; decide) (by rw [hpcW]; decide) ?_
    rw [hpcW, read_congr _ s.mem _ 4 (fun j hj => hromW _ (by simp only [ROM_END, Image.halt]; bv_omega))]
    exact hhalt
  · obtain ⟨m, W, hrun, hst⟩ := hbad hc
    exact stuck_never_halts s W m hrun hst.step_none _ (by decide) (by decide) hhalt

/-- With a wrong claim or path the run ends at `zksync_os_finish_error`. -/
theorem program_correct_stuck : StuckOnBadClaim Image.bytes := fun s x y0 y1 y2 y3 v0 v1 v2 v3 root path rest hpc himg
    hram hin hd hxP hy0p hy1p hy2p hy3p hc => (program_correct_run s x y0 y1 y2 y3 v0 v1 v2 v3 root path rest hpc himg hram
      hin hd hxP hy0p hy1p hy2p hy3p).2.2 hc

end RV
