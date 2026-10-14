import Slop.RV.Program
import Slop.RV.Link
import Slop.RV.PolyZMod
import Slop.RV.Halt

/-! The final theorem: link check (image bytes = the code and the `.rodata` table the proofs use) + whole-program run
+ ZMod bridge + the final self-jump (`jal zero, .`, the last word of `zksync_os_finish_success_extended`) keeps
everything in place. -/

namespace RV

set_option maxRecDepth 1000000 in
theorem program_correct : ProgramCorrect := by
  intro s x hpc himg _ hin hx
  have hs : Image.bytes.size < 2 ^ 32 := by decide +kernel
  have h := program_run s x hpc
    (codeAt_of_bytesW himg 0 Code.boot (by decide +kernel) hs (by decide +kernel))
    (codeAt_of_bytesW himg 0x3c4 Code.init (by decide +kernel) hs (by decide +kernel))
    (codeAt_of_bytesW himg 0x44c Code.memcpy (by decide +kernel) hs (by decide +kernel))
    (codeAt_of_bytesW himg 0xd8 Code.combine (by decide +kernel) hs (by decide +kernel))
    (codeAt_of_bytesW himg 0x144 Code.inc (by decide +kernel) hs (by decide +kernel))
    (codeAt_of_bytesW himg 0x120 Code.double (by decide +kernel) hs (by decide +kernel))
    (codeAt_of_bytesW himg 0x1a4 Code.poly_eval (by decide +kernel) hs (by decide +kernel))
    (codeAt_of_bytesW himg 0x168 Code.mul_mod (by decide +kernel) hs (by decide +kernel))
    (codeAt_of_bytesW himg 0xa4 Code.add_mod (by decide +kernel) hs (by decide +kernel))
    (codeAt_of_bytesW himg 0x2c8 Code.finish_success (by decide +kernel) hs (by decide +kernel))
    (codeAt_of_bytesW himg 0x340 Code.finish_success_extended (by decide +kernel) hs (by decide +kernel))
    (codeAt_of_bytesW himg 0x1e7c Code.COEFFS (by decide +kernel) hs (by decide +kernel))
    hx hin
  obtain ⟨n, s', hrun, hpc', ha0, ha1, ha1', hzero, hw⟩ := h
  refine ⟨n, s', hrun, hpc', ?_, ha1, ?_, hzero, ?_⟩
  · rw [ha0]; rfl
  · rw [← polyW_zmod, ZMod.natCast_eq_natCast_iff']
    exact ha1'
  · exact halt_forever s' (by rw [hpc']; decide) (by rw [hpc']; decide) (by rw [hpc']; exact hw)

end RV
