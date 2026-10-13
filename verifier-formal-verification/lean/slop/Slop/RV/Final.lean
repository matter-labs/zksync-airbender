import Slop.RV.Program
import Slop.RV.Link
import Slop.RV.PolyZMod

/-! The final theorem: link check (image bytes = the code the proofs use) + whole-program run + ZMod bridge. -/

namespace RV

theorem program_correct : ProgramCorrect := by
  intro s x hpc himg hin hx
  have hs : Image.bytes.size < 2 ^ 32 := by decide +kernel
  have h := program_run s x hpc
    (codeAt_of_bytes himg 0 Code.boot (by decide +kernel) hs (by decide +kernel))
    (codeAt_of_bytes himg 0xbc Code.combine (by decide +kernel) hs (by decide +kernel))
    (codeAt_of_bytes himg 0x128 Code.inc (by decide +kernel) hs (by decide +kernel))
    (codeAt_of_bytes himg 0x104 Code.double (by decide +kernel) hs (by decide +kernel))
    (codeAt_of_bytes himg 0x188 Code.poly_eval (by decide +kernel) hs (by decide +kernel))
    (codeAt_of_bytes himg 0x14c Code.mul_mod (by decide +kernel) hs (by decide +kernel))
    (codeAt_of_bytes himg 0x88 Code.add_mod (by decide +kernel) hs (by decide +kernel))
    (codeAt_of_bytes himg 0x204 Code.COEFFS (by decide +kernel) hs (by decide +kernel))
    hin hx
  obtain ⟨n, s', hh⟩ := h
  refine ⟨n, s', hh.1, hh.2.1, ?_, hh.2.2.2.1, ?_, by rw [hh.2.2.2.2.2, hh.2.1]⟩
  · rw [hh.2.2.1]; rfl
  · rw [← polyW_zmod, ZMod.natCast_eq_natCast_iff']
    exact hh.2.2.2.2.1

end RV
