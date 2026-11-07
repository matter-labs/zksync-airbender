import Airbender.Review.Trace.Families.ReducedMachine.CSRArgument

namespace Tests.NativeReducedCSRArgument
open Airbender Trace ReducedMachine Native
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false
private abbrev embed := RingHom.id (ZMod mersenne31Modulus)
private def w (i : Nat) : ZMod mersenne31Modulus :=
  if i=94 then 1991 else if i=93 then 4660 else if i=2 then 4 else if i=3 then 2 else 0
private def ch : CSRArgumentChallenges (ZMod mersenne31Modulus) := ⟨11,3,5,7⟩

/-- This particular unrolled prover passes sequence0, not the chunk sequence. -/
theorem selected_sequence_zero : csrUnrolledSequence = 0 ∧ csrUnrolledSequenceHigh = 0 := by decide

theorem actual_caller_key : csrCallerKey embed (csrCallerObservation (.mk .reduced w)) =
    ⟨1991,4660,7,2⟩ := by decide

/-- Independently computed affine stage2 reference. -/
theorem stage_two_numeric : csrStageTwoArgument embed ch w = 16031 := by decide

/-- Witness scaling acts before the literal timestamp offset is added. -/
theorem stage_three_numeric : csrStageThreeArgument embed ch 2 w = 32036 := by decide

theorem gamma_unscaled : csrStageThreeArgument embed ⟨11,0,0,0⟩ 7 (fun _ => 0) = 11 := by decide

theorem literal_offset_unscaled :
    csrStageThreeArgument embed ⟨0,0,5,0⟩ 2 (fun i => if i=2 then 4 else 0) = 55 := by decide

/-- The identity is polynomial and does not silently cancel an arbitrary tau. -/
theorem zero_scaling : csrStageThreeArgument embed ch 0 w = 26 := by decide

/-- Adding a hypothetical sequence1 shift again would change the actual key. -/
theorem no_double_sequence_shift : (csrNormalizedCallerKey embed 1 w).high ≠ 66 := by decide

/-- Arbitrary challenge compression is not injective: this remains a separate
    cryptographic/statement boundary, never a tuple-matching proof premise. -/
theorem compression_can_collide :
    csrArgument (R := ZMod mersenne31Modulus) ⟨0,0,0,0⟩ ⟨1991,0,7,0⟩ =
      csrArgument ⟨0,0,0,0⟩ ⟨1991,65535,11,0⟩ ∧
    (⟨1991,0,7,0⟩ : CSRArgumentKey (ZMod mersenne31Modulus)) ≠ ⟨1991,65535,11,0⟩ := by decide

end Tests.NativeReducedCSRArgument
