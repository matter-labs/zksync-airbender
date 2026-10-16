import Slop.RV.Main.Run
import Slop.RV.InitMop
import Slop.RV.Ext4Poly.Impl
import Slop.RV.Link

/-! The final theorem for the plain image: link check (image bytes = the code and tables the proofs use), then the
whole program (`main_run`). -/

namespace RV
open Spec

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem program_correct : ProgramCorrect := by
  intro s x y0 y1 y2 y3 hpc himg hram hx hxP hy0 hy1 hy2 hy3 hy0p hy1p hy2p hy3p
  have hs : Image.bytes.size < 2 ^ 32 := by decide +kernel
  have cStart := codeAt_of_bytesW himg 0 Code.start (by decide +kernel) hs (by decide +kernel)
  have cMain := codeAt_of_bytesW himg 0x38 Code.main (by decide +kernel) hs (by decide +kernel)
  have cInit := codeAt_of_bytesW himg 0x23a8 Code.init (by decide +kernel) hs (by decide +kernel)
  have cMemcpy := codeAt_of_bytesW himg 0x2430 Code.memcpy (by decide +kernel) hs (by decide +kernel)
  have cComb := codeAt_of_bytesW himg 0x2174 Code.combine (by decide +kernel) hs (by decide +kernel)
  have cInc := codeAt_of_bytesW himg 0x21e0 Code.inc (by decide +kernel) hs (by decide +kernel)
  have cDbl := codeAt_of_bytesW himg 0x21bc Code.double (by decide +kernel) hs (by decide +kernel)
  have cPoly := codeAt_of_bytesW himg 0x20f8 Code.poly_eval (by decide +kernel) hs (by decide +kernel)
  have cMul := codeAt_of_bytesW himg 0x20bc Code.mul_mod (by decide +kernel) hs (by decide +kernel)
  have cAdd := codeAt_of_bytesW himg 0x2088 Code.add_mod (by decide +kernel) hs (by decide +kernel)
  have cEP := codeAt_of_bytesW himg 0x1e58 Code.ext4_poly (by decide +kernel) hs (by decide +kernel)
  have cHor := codeAt_of_bytesW himg 0x17cc Code.ext4_horner (by decide +kernel) hs (by decide +kernel)
  have cMA := codeAt_of_bytesW himg 0x1874 Code.ext4_mul_add (by decide +kernel) hs (by decide +kernel)
  have cBl := codeAt_of_bytesW himg 0x18c Code.blake2s_compress (by decide +kernel) hs (by decide +kernel)
  have cFin := codeAt_of_bytesW himg 0x2284 Code.finish_success (by decide +kernel) hs (by decide +kernel)
  have cExt := codeAt_of_bytesW himg 0x22fc Code.finish_success_extended (by decide +kernel) hs (by decide +kernel)
  have cCoef := codeAt_of_bytesW himg 0x3e60 Code.COEFFS (by decide +kernel) hs (by decide +kernel)
  have cCoef4 := codeAt_of_bytesW himg (0x3e60 + 0x190) Code.COEFFS4 (by decide +kernel) hs (by decide +kernel)
  simp only [BitVec.ofNat_eq_ofNat] at *
  have e : ∀ k, BitVec.ofNat 32 (Image.INPUT + k) = 0x1401000#32 + BitVec.ofNat 32 k := fun k => by
    simp only [Image.INPUT]; bv_omega
  rw [show BitVec.ofNat 32 Image.INPUT = 0x1401000#32 from rfl] at hx
  rw [e] at hy0 hy1 hy2 hy3
  simp only [BitVec.reduceAdd] at hy0 hy1 hy2 hy3
  obtain ⟨m, W, hrun, hpcW, r10, r11, r11', r12, rl, r16, r17, rz, hromW⟩ :=
    main_run s Code.main Code.init Code.ext4_poly
      [(0x1e58#32 + 4294965620#32, Code.ext4_horner), (0x1e58#32 + 4294965620#32 + 168#32, Code.ext4_mul_add)] 192
      0x23a8#32 0x2174#32 0x20f8#32 0x1e58#32 0x18c#32 0x2284#32 0x3e60#32 x y0 y1 y2 y3
      (init_run 0x23a8#32 (by decide) (by decide)) (by decide +kernel) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide)
      (ext4_poly_impl 0x1e58#32 (by decide) (by decide)) (by decide +kernel) (by decide) (by decide)
      (by intro c hc; simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
          rcases hc with h | h <;> subst h <;> decide +kernel)
      (by decide) (by decide +kernel) (by decide) (by decide) (by decide +kernel)
      rfl rfl rfl rfl rfl rfl
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel)
      hpc cStart cMain cInit cMemcpy cComb cInc cDbl cPoly cMul cAdd cCoef cCoef4 cEP
      (by
        intro c hc; simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with h | h <;> subst h
        · exact cHor
        · exact cMA)
      cBl cFin cExt hram hx hy0 hy1 hy2 hy3 hxP hy0p hy1p hy2p hy3p
  refine ⟨m, W, hrun, by rw [hpcW]; rfl, r10, r11, r11', r12, rl, r16, r17, rz, ?_⟩
  refine halt_forever W (by rw [hpcW]; decide) (by rw [hpcW]; decide) ?_
  rw [hpcW, read_congr _ s.mem _ 4 (fun j hj => hromW _ (by simp only [ROM_END]; bv_omega))]
  have := cExt 32 (by decide)
  simpa [Code.finish_success_extended] using this

end RV
