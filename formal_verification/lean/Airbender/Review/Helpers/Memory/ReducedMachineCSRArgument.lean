import Airbender.Review.Helpers.Memory.ReducedMachineCSRCallers

namespace Airbender.ReducedMachine.Native
open Trace Reference.RiscV.Sail
set_option autoImplicit false

/-- The selected native unrolled prover passes literal sequence0 to its cache.
    For the imported trace2^23/three-access geometry the cache shift is6.
    These are reviewed source-reference definitions, not general Rust refinement. -/
def csrUnrolledSequence : Nat := 0
def csrUnrolledSequenceHigh : ZMod mersenne31Modulus :=
  ((csrUnrolledSequence * 2^(23+2-19) : Nat) : ZMod mersenne31Modulus)

structure CSRArgumentKey (R : Type) where
  kind : R
  abi : R
  low : R
  high : R
  deriving DecidableEq

structure CSRArgumentChallenges (R : Type) where
  gamma : R
  abi : R
  low : R
  high : R

def csrArgument {R : Type} [CommRing R] (ch : CSRArgumentChallenges R) (key : CSRArgumentKey R) : R :=
  ch.gamma + key.kind + ch.abi*key.abi + ch.low*key.low + ch.high*key.high

def csrCallerKey {R : Type} [CommRing R] (embed : ZMod mersenne31Modulus →+* R)
    (caller : CSRCallerObservation) : CSRArgumentKey R :=
  ⟨embed caller.request.kind,embed (caller.request.offsetHigh.getD 0),
    embed caller.time.1,embed caller.time.2⟩

/-- Native stage2 aggregates the observed ABI and offset timestamp, with gamma. -/
def csrStageTwoArgument {R : Type} [CommRing R] (embed : ZMod mersenne31Modulus →+* R)
    (ch : CSRArgumentChallenges R) (w : Nat → ZMod mersenne31Modulus) : R :=
  csrArgument ch ⟨embed (w 94),embed (w 93),embed (w 2+3),embed (w 3)⟩

/-- Native quotient computation scales all witness-dependent linear terms by
    tau. Gamma and literal offset/sequence contributions are added afterwards. -/
def csrStageThreeArgument {R : Type} [CommRing R] (embed : ZMod mersenne31Modulus →+* R)
    (ch : CSRArgumentChallenges R) (tau : R) (w : Nat → ZMod mersenne31Modulus) : R :=
  (embed (w 94)+ch.abi*embed (w 93)+ch.low*embed (w 2)+ch.high*embed (w 3))*tau +
    ch.gamma + ch.low*3 + ch.high*embed csrUnrolledSequenceHigh

def csrNormalizedCallerKey {R : Type} [CommRing R] (embed : ZMod mersenne31Modulus →+* R)
    (tau : R) (w : Nat → ZMod mersenne31Modulus) : CSRArgumentKey R :=
  ⟨embed (w 94)*tau,embed (w 93)*tau,
    embed (w 2)*tau+3,embed (w 3)*tau+embed csrUnrolledSequenceHigh⟩

/-- Per-row caller-key/denominator correspondence only. This neither assumes
    compression injectivity nor states a worker ledger, LDE or verifier result. -/
def CSRCallerArgumentProjection {R : Type} [CommRing R]
    (embed : ZMod mersenne31Modulus →+* R) (ch : CSRArgumentChallenges R)
    (trace : Data mersenne31Modulus NativeReducedFamily) (callers : List CSRCallerObservation) : Prop :=
  ∀ caller ∈ callers, ∃ row ∈ trace.rows,
    caller = csrCallerObservation row ∧
    csrCallerKey embed caller = csrNormalizedCallerKey embed 1 row.assignment ∧
    csrStageTwoArgument embed ch row.assignment = csrArgument ch (csrCallerKey embed caller) ∧
    (∀ tau, csrStageThreeArgument embed ch tau row.assignment =
      csrArgument ch (csrNormalizedCallerKey embed tau row.assignment)) ∧
    csrStageThreeArgument embed ch 1 row.assignment = csrStageTwoArgument embed ch row.assignment

end Airbender.ReducedMachine.Native
