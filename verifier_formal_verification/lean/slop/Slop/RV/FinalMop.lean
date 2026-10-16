import Slop.RV.Main.Run
import Slop.RV.InitMop
import Slop.RV.Ext4PolyMop
import Slop.RV.MulAddMop
import Slop.RV.Link
import Slop.RV.Code.main_mop

/-! The final theorem for the `mop` image: link check (image bytes = the code and tables the proofs use), then the
whole program (`main_run`). -/

namespace RV
open Spec

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem program_correct_mop : ProgramCorrectMop := by
  intro s x y0 y1 y2 y3 rest hpc himg hram hin hxP hy0p hy1p hy2p hy3p
  have hs : ImageMop.bytes.size < 2 ^ 32 := by decide +kernel
  have cStart := codeAt_of_bytesW himg 0 Code.start (by decide +kernel) hs (by decide +kernel)
  have cMain := codeAt_of_bytesW himg 0x38 Code.main_mop (by decide +kernel) hs (by decide +kernel)
  have cInit := codeAt_of_bytesW himg 0x1d18 Code.init_mop (by decide +kernel) hs (by decide +kernel)
  have cMemcpy := codeAt_of_bytesW himg 0x1da0 Code.memcpy (by decide +kernel) hs (by decide +kernel)
  have cComb := codeAt_of_bytesW himg 0x1ae4 Code.combine (by decide +kernel) hs (by decide +kernel)
  have cInc := codeAt_of_bytesW himg 0x1b50 Code.inc (by decide +kernel) hs (by decide +kernel)
  have cDbl := codeAt_of_bytesW himg 0x1b2c Code.double (by decide +kernel) hs (by decide +kernel)
  have cPoly := codeAt_of_bytesW himg 0x1a68 Code.poly_eval (by decide +kernel) hs (by decide +kernel)
  have cMul := codeAt_of_bytesW himg 0x1a2c Code.mul_mod (by decide +kernel) hs (by decide +kernel)
  have cAdd := codeAt_of_bytesW himg 0x19f8 Code.add_mod (by decide +kernel) hs (by decide +kernel)
  have cEP := codeAt_of_bytesW himg 0x1938 Code.ext4_poly_mop (by decide +kernel) hs (by decide +kernel)
  have cHor := codeAt_of_bytesW himg 0x17cc Code.ext4_horner (by decide +kernel) hs (by decide +kernel)
  have cMA := codeAt_of_bytesW himg 0x1874 Code.ext4_mul_add_mop (by decide +kernel) hs (by decide +kernel)
  have cBl := codeAt_of_bytesW himg 0x18c Code.blake2s_compress (by decide +kernel) hs (by decide +kernel)
  have cFin := codeAt_of_bytesW himg 0x1bf4 Code.finish_success (by decide +kernel) hs (by decide +kernel)
  have cExt := codeAt_of_bytesW himg 0x1c6c Code.finish_success_extended (by decide +kernel) hs (by decide +kernel)
  have cCoef := codeAt_of_bytesW himg 0x37d0 Code.COEFFS (by decide +kernel) hs (by decide +kernel)
  have cCoef4 := codeAt_of_bytesW himg (0x37d0 + 0x190) Code.COEFFS4 (by decide +kernel) hs (by decide +kernel)
  simp only [BitVec.ofNat_eq_ofNat] at *
  obtain ⟨m, W, hrun, hpcW, r10, r11, r11', r12, rl, r16, r17, rz, hromW⟩ :=
    main_run s Code.main_mop Code.init_mop Code.ext4_poly_mop
      [(0x1938#32 + 4294966932#32, Code.ext4_horner), (0x1938#32 + 4294966932#32 + 168#32, Code.ext4_mul_add_mop)] 112
      0x1d18#32 0x1ae4#32 0x1a68#32 0x1938#32 0x18c#32 0x1bf4#32 0x37d0#32 x y0 y1 y2 y3
      (init_run_mop 0x1d18#32 (by decide) (by decide)) (by decide +kernel) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide)
      (ext4_poly_mop_impl 0x1938#32 (by decide) (by decide)) (by decide +kernel) (by decide) (by decide)
      (by intro c hc; simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
          rcases hc with h | h <;> subst h <;> decide +kernel)
      (by decide) (by decide +kernel) (by decide) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel)
      hpc cStart cMain cInit cMemcpy cComb cInc cDbl cPoly cMul cAdd cCoef cCoef4 cEP
      (by
        intro c hc; simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with h | h <;> subst h
        · exact cHor
        · exact cMA)
      cBl cFin cExt hram rest hin hxP hy0p hy1p hy2p hy3p
  refine ⟨m, W, hrun, by rw [hpcW]; rfl, r10, r11, r11', r12, rl, r16, r17, rz, ?_⟩
  refine halt_forever W (by rw [hpcW]; decide) (by rw [hpcW]; decide) ?_
  rw [hpcW, read_congr _ s.mem _ 4 (fun j hj => hromW _ (by simp only [ROM_END]; bv_omega))]
  have := cExt 32 (by decide)
  simpa [Code.finish_success_extended] using this

end RV
