import Airbender.Review.Circuits.ReducedMachine.CallerMixedQueries

namespace Airbender.NativeCallerValidity
open Airbender.NativeCallerRequests (F)
open Airbender.ReducedMachine.Native

/-- The competing lookup major flags; other decoder bits remain unchanged. -/
def competing (w : Nat → F) : Vector F 6 := #v[w 22,w 23,w 25,w 27,w 29,w 31]

/-- Derived request validity on all ordinary rows, including execute0. This is
    neither physical activity nor original CSR/Sail execution or per-call matching. -/
structure RowEffects (w : Nat → F) : Prop where
  prior : Airbender.NativeCallerMixedQueries.RuntimeRowEffects w
  boolean : (csrRequest w).multiplicity = 0 ∨ (csrRequest w).multiplicity = 1
  request : csrRequest w = ⟨0,0,some 0,3⟩ ∨ csrRequest w = ⟨1,1991,some (w 36),3⟩
  inputs : (csrRequest w).multiplicity ≠ 0 → w 9 = 1991 ∧ w 65 = 1 ∧ (w 36).val < 65536
  isolation : (csrRequest w).multiplicity ≠ 0 → competing w = #v[0,0,0,0,0,0]

/-- Every original ordinary caller occurrence, without activity/request filtering. -/
def Effects {R : Type} [Field R] (proofs : List (Airbender.NativeInitializationBatch.Proof R)) : Prop :=
  ∀ w ∈ Airbender.NativeTokenLedger.mainRows (Airbender.NativeInitializationBatch.mainProofs proofs), RowEffects w
end Airbender.NativeCallerValidity
