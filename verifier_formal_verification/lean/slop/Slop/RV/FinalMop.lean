import Slop.RV.Start
import Slop.RV.MainAMop
import Slop.RV.MainBMop
import Slop.RV.Ext4PolyMop
import Slop.RV.Link
import Slop.RV.PolyZMod
import Slop.RV.Halt

/-! The final theorem for the `mop` image: link check (image bytes = the code and tables the proofs use), then
`_start` → `main` (part A: `init`, `combine`, `poly_eval`; part B: `ext4_poly`, the outputs) → the final self-jump. -/

namespace RV
open Spec

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem program_correct_mop : ProgramCorrectMop := by
  intro s x y0 y1 y2 y3 hpc himg _ hx hxP hy0 hy1 hy2 hy3 hy0p hy1p hy2p hy3p
  have hs : ImageMop.bytes.size < 2 ^ 32 := by decide +kernel
  have cStart := codeAt_of_bytesW himg 0 Code.start (by decide +kernel) hs (by decide +kernel)
  have cMain := codeAt_of_bytesW himg 0x38 Code.main_mop (by decide +kernel) hs (by decide +kernel)
  have cInit := codeAt_of_bytesW himg 0x644 Code.init_mop (by decide +kernel) hs (by decide +kernel)
  have cMemcpy := codeAt_of_bytesW himg 0x6cc Code.memcpy (by decide +kernel) hs (by decide +kernel)
  have cComb := codeAt_of_bytesW himg 0x410 Code.combine (by decide +kernel) hs (by decide +kernel)
  have cInc := codeAt_of_bytesW himg 0x47c Code.inc (by decide +kernel) hs (by decide +kernel)
  have cDbl := codeAt_of_bytesW himg 0x458 Code.double (by decide +kernel) hs (by decide +kernel)
  have cPoly := codeAt_of_bytesW himg 0x394 Code.poly_eval (by decide +kernel) hs (by decide +kernel)
  have cMul := codeAt_of_bytesW himg 0x358 Code.mul_mod (by decide +kernel) hs (by decide +kernel)
  have cAdd := codeAt_of_bytesW himg 0x324 Code.add_mod (by decide +kernel) hs (by decide +kernel)
  have cEP := codeAt_of_bytesW himg 0x264 Code.ext4_poly_mop (by decide +kernel) hs (by decide +kernel)
  have cHor := codeAt_of_bytesW himg 0xf8 Code.ext4_horner (by decide +kernel) hs (by decide +kernel)
  have cMA := codeAt_of_bytesW himg 0x1a0 Code.ext4_mul_add_mop (by decide +kernel) hs (by decide +kernel)
  have cFin := codeAt_of_bytesW himg 0x548 Code.finish_success (by decide +kernel) hs (by decide +kernel)
  have cExt := codeAt_of_bytesW himg 0x5c0 Code.finish_success_extended (by decide +kernel) hs (by decide +kernel)
  have cCoef := codeAt_of_bytesW himg 0x20fc Code.COEFFS (by decide +kernel) hs (by decide +kernel)
  have cCoef4 := codeAt_of_bytesW himg (0x20fc + 0x190) Code.COEFFS4 (by decide +kernel) hs (by decide +kernel)
  simp only [BitVec.ofNat_eq_ofNat] at *
  refine run_cont (start_run s hpc cStart) ?_
  intro S0 ⟨hpc0, h20, hra0, hm0⟩
  have hrom0 : ∀ b : Word, b.toNat < ROM_END → S0.mem b = s.mem b := fun b hb => hm0 b (by simp only [ROM_END] at hb; omega)
  have rd : ∀ a : Word, 0x1401000 ≤ a.toNat → a.toNat + 4 ≤ 0x1401014 → read S0.mem a 4 = read s.mem a 4 :=
    fun a h1 h2 => read_congr _ _ _ _ (fun j hj => hm0 _ (by bv_omega))
  have e : ∀ k, BitVec.ofNat 32 (ImageMop.INPUT + k) = 0x1401000#32 + BitVec.ofNat 32 k := fun k => by
    simp only [ImageMop.INPUT]; bv_omega
  rw [show BitVec.ofNat 32 ImageMop.INPUT = 0x1401000#32 from rfl] at hx
  rw [e] at hy0 hy1 hy2 hy3
  simp only [BitVec.reduceAdd] at hy0 hy1 hy2 hy3
  refine run_cont (main_a_mop S0 x y0 y1 y2 y3 hpc0 h20 hra0
    (codeAt_of_rom cMain (by decide) hrom0) (codeAt_of_rom cInit (by decide) hrom0)
    (codeAt_of_rom cMemcpy (by rw [memcpy_length]; decide) hrom0) (codeAt_of_rom cComb (by decide) hrom0)
    (codeAt_of_rom cInc (by decide) hrom0) (codeAt_of_rom cDbl (by decide) hrom0)
    (codeAt_of_rom cPoly (by decide) hrom0) (codeAt_of_rom cMul (by decide) hrom0)
    (codeAt_of_rom cAdd (by decide) hrom0) (codeAt_of_rom cCoef (by rw [coeffs_length]; decide) hrom0)
    (codeAt_of_rom cCoef4 (by rw [coeffs4_length]; decide) hrom0)
    ((rd _ (by decide) (by decide)).trans hx) ((rd _ (by decide) (by decide)).trans hy0)
    ((rd _ (by decide) (by decide)).trans hy1) ((rd _ (by decide) (by decide)).trans hy2)
    ((rd _ (by decide) (by decide)).trans hy3) hxP) ?_
  intro T ⟨hpcT, h2T, h18T, h9a, h9b, h19T, h20T, h21T, h22T, htabT, hromT⟩
  have hromT' : ∀ b : Word, b.toNat < ROM_END → T.mem b = s.mem b := fun b hb => (hromT b hb).trans (hrom0 b hb)
  refine run_cont (main_b_mop T _ _ y0 y1 y2 y3 Code.ext4_poly_mop
    [(0x264#32 + 4294966932#32, Code.ext4_horner), (0x264#32 + 4294966932#32 + 168#32, Code.ext4_mul_add_mop)] 112
    (ext4_poly_mop_impl 0x264#32 (by decide) (by decide)) (by decide) (by decide) ?_ hpcT h2T h18T rfl
    h19T h20T h21T h22T htabT (codeAt_of_rom cMain (by decide) hromT') (codeAt_of_rom cEP (by decide) hromT') ?_
    (codeAt_of_rom cFin (by decide) hromT') (codeAt_of_rom cExt (by decide) hromT') hy0p hy1p hy2p hy3p) ?_
  · intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with h | h <;> subst h <;> decide
  · intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with h | h <;> subst h
    · exact codeAt_of_rom cHor (by decide) hromT'
    · exact codeAt_of_rom cMA (by decide) hromT'
  intro W ⟨hpcW, h10W, h11W, hcW, hlW, hzW, hromW⟩
  refine ⟨0, W, rfl, ?_, ?_, ?_, ?_, hcW, hlW, hzW, ?_⟩
  · rw [hpcW]; rfl
  · rw [h10W]; rfl
  · rw [h11W]; exact h9a
  · rw [h11W, ← polyW_zmod, ZMod.natCast_eq_natCast_iff']; exact h9b
  · refine halt_forever W (by rw [hpcW]; decide) (by rw [hpcW]; decide) ?_
    rw [hpcW, read_congr _ s.mem _ 4 (fun j hj => by
      rw [hromW _ (by simp only [ROM_END]; bv_omega), hromT' _ (by simp only [ROM_END]; bv_omega)])]
    have := cExt 32 (by decide)
    simpa [Code.finish_success_extended] using this

end RV
