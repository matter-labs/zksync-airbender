import Airbender.Review.Circuits.ReducedMachine.CallerRequests

namespace Airbender.NativeCallerClockDomain
open Airbender.ReducedMachine.Native
abbrev F := Airbender.NativeCallerRequests.F

/-- Actual raw caller observation, including execute0 physical rows. -/
def time (w : Nat → F) : Trace.Timestamp := Trace.timeOfPair (w 2+3,w 3)

/-- Canonical field wrap is retained as the explicit M31-minus-one sentinel.
    This domain is not a19bit bound or a chronological memory-history claim. -/
structure Domain (clock : Trace.Timestamp) : Prop where
  low : clock.lo < 1048575 ∨ clock.lo = mersenne31Modulus-1
  high : clock.hi < 524288 ∨ clock.hi = mersenne31Modulus-1
  lowWrap : clock.lo = mersenne31Modulus-1 → clock.hi < 524288
  highWrap : clock.hi = mersenne31Modulus-1 → 524287 ≤ clock.lo ∧ clock.lo < 1048575

/-- Exact endpoint alternatives from the actual Boolean carry equations.
    Both raw wrap cases remain; no execute or expected clock premise. -/
def EndpointCases (w : Nat → F) : Prop :=
  (((time w).lo+1 = (w 15).val ∨ ((time w).lo = mersenne31Modulus-1 ∧ (w 15).val = 0)) ∧
    (time w).hi = (w 16).val) ∨
  ((time w).lo+1 = (w 15).val+524288 ∧
    ((time w).hi+1 = (w 16).val ∨ ((time w).hi = mersenne31Modulus-1 ∧ (w 16).val = 0)))

structure RowEffects (w : Nat → F) : Prop where
  final : (w 15).val < 524288 ∧ (w 16).val < 524288
  endpoints : EndpointCases w
  domain : Domain (time w)

/-- All ordinary physical rows on the SAME actual list; no activity filter. -/
def Effects {R : Type} [Field R] (proofs : List (Airbender.NativeInitializationBatch.Proof R)) : Prop :=
  ∀ w ∈ Airbender.NativeTokenLedger.mainRows (Airbender.NativeInitializationBatch.mainProofs proofs), RowEffects w
end Airbender.NativeCallerClockDomain
