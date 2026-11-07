import Airbender.Review.Helpers.Memory.ReducedMachineCSRArgument
import Airbender.Proofs.ReducedMachine.NativeCSRCallerClock

namespace Airbender.ReducedMachine.NativeCSRArgumentProofs
open Native Trace
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- Kernel-check the imported geometry used by the reviewed native cache call. -/
theorem geometry : importedConstraintsSetupColumns.traceLength = 2^23 ∧
    importedConstraintsMemoryPorts.size = 3 ∧ 2^(23+2-19) = (64 : Nat) := by decide

/-- The selected native unrolled constructor has no additional sequence-high shift. -/
theorem sequence_high_zero : csrUnrolledSequenceHigh = 0 := rfl

/-- Exact imported caller coordinates identify the pre-compression key. -/
theorem caller_key {R : Type} [CommRing R] (embed : ZMod mersenne31Modulus →+* R)
    (w : Nat → ZMod mersenne31Modulus) :
    csrCallerKey embed (csrCallerObservation (.mk .reduced w)) =
      csrNormalizedCallerKey embed 1 w := by
  have three : embed (3 : ZMod mersenne31Modulus) = (3 : R) := by
    have literal : (3 : ZMod mersenne31Modulus) = 1+1+1 := by norm_num
    rw [literal,map_add,map_add,map_one]
    ring
  simp [csrCallerKey,NativeCSRCallerProofs.observation_columns,csrNormalizedCallerKey,
    sequence_high_zero,map_add,three]

theorem stage_two {R : Type} [CommRing R] (embed : ZMod mersenne31Modulus →+* R)
    (ch : CSRArgumentChallenges R) (w : Nat → ZMod mersenne31Modulus) :
    csrStageTwoArgument embed ch w = csrArgument ch (csrCallerKey embed (csrCallerObservation (.mk .reduced w))) := by
  rw [NativeCSRCallerProofs.observation_columns]
  rfl

/-- Preserve the native order of homogenization: literal offsets and gamma
    remain outside the witness scaling. No inverse or nonzero premise is needed. -/
theorem stage_three {R : Type} [CommRing R] (embed : ZMod mersenne31Modulus →+* R)
    (ch : CSRArgumentChallenges R) (tau : R) (w : Nat → ZMod mersenne31Modulus) :
    csrStageThreeArgument embed ch tau w = csrArgument ch (csrNormalizedCallerKey embed tau w) := by
  simp only [csrStageThreeArgument,csrArgument,csrNormalizedCallerKey]
  ring

/-- Specialization at unit scaling agrees with the actual stage2 caller tuple.
    This is not a claim that every protocol evaluation has tau=1. -/
theorem unit_scaling {R : Type} [CommRing R] (embed : ZMod mersenne31Modulus →+* R)
    (ch : CSRArgumentChallenges R) (w : Nat → ZMod mersenne31Modulus) :
    csrStageThreeArgument embed ch 1 w = csrStageTwoArgument embed ch w := by
  rw [stage_three,← caller_key,stage_two]

end Airbender.ReducedMachine.NativeCSRArgumentProofs
