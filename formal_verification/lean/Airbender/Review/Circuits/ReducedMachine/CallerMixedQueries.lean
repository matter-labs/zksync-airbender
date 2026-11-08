import Airbender.Review.Circuits.ReducedMachine.CallerRequests
import Airbender.Review.Circuits.ReducedMachine.Tables.RuntimePool

namespace Airbender.NativeCallerMixedQueries
open Airbender.NativeCallerRequests Airbender.ReducedMachine.Native

/-- The four actual dynamic tuples, including every original selector. -/
def query (w : Nat → F) (slot : Fin 4) : Vector F 4 :=
  #v[w (100 + 4 * slot.val),w (101 + 4 * slot.val),w (102 + 4 * slot.val),w (103 + 4 * slot.val)]

/-- Full mixed opcode contributions; no mask, activity or orthogonality premise.
    These are query observables, not an execution or worker-result reference. -/
def normalized (w : Nat → F) : Vector (Vector F 4) 4 := #v[
  #v[w 9 * w 24 + w 61 * w 25 + w 61 * w 31 + w 62 * w 27 + w 69 * w 23 + w 22 * w 55 + w 29 * w 47,
      w 22 * w 58 + w 23 * w 64 + w 24 * w 64 + w 25 * w 64 + w 27 * w 64 + w 29 * w 64 + w 31 * w 64,
      w 22 * w 64 + w 23 * w 65 + w 24 * w 65 + w 25 * w 65 + w 27 * w 65 + w 29 * w 65 + w 31 * w 65,
      w 11 * w 22 + 17 * w 23 + 25 * w 24 + 17 * w 25 + 23 * w 27 + 47 * w 29 + 18 * w 31],
  #v[w 11 * w 23 + w 61 * w 27 + w 62 * w 31 + -8388608 * w 22 * w 55 + 8388608 * w 22 * w 35 + 8 * w 23 * w 63 + 16 * w 23 * w 68 + 32 * w 23 * w 56 + 64 * w 23 * w 59 + 65536 * w 27 * w 65 + 2097152 * w 29 * w 33 + 65536 * w 29 * w 64 + w 29 * w 35,
      8388608 * w 22 * w 47 + -8388608 * w 22 * w 58 + w 23 * w 66 + w 27 * w 66 + w 29 * w 66 + w 31 * w 66,
      w 22 * w 65 + w 23 * w 67 + w 27 * w 67 + w 29 * w 67 + w 31 * w 67,
      w 11 * w 22 + 22 * w 23 + 24 * w 27 + 37 * w 29 + 23 * w 31],
  #v[-256 * w 22 * w 57 + w 22 * w 36 + 2097152 * w 29 * w 33 + 65536 * w 29 * w 64 + w 29 * w 36,
      w 22 * w 48 + -256 * w 22 * w 60 + w 29 * w 75,
      w 22 * w 66 + w 29 * w 76,
      w 11 * w 22 + 37 * w 29],
  #v[w 22 * w 57 + 2 * w 29 * w 32 + w 29 * w 56 + 4 * w 29 * w 64,
      w 22 * w 60 + w 29 * w 79,
      w 22 * w 67 + w 29 * w 80,
      w 11 * w 22 + 20 * w 29]
 ]

structure RowEffects (w : Nat → F) : Prop where
  caller : Airbender.NativeCallerRequests.RowEffects w
  exact : ∀ slot, query w slot = (normalized w)[slot]
  presentSecond : (csrRequest w).multiplicity ≠ 0 →
    w 101 = w 22 * w 58 + w 23 + 1 + w 25 + w 27 + w 29 + w 31
  presentThird : (csrRequest w).multiplicity ≠ 0 →
    w 102 = w 22 + (w 23 + 1 + w 25 + w 27 + w 29 + w 31) * w 65
  lastTags : w 111 - w 115 = 17 * w 29

structure RuntimeRowEffects (w : Nat → F) : Prop where
  queries : RowEffects w
  membership : ∀ slot : Fin 4, (Airbender.ReducedMachine.NativeRuntimePool.table (p := mersenne31Modulus)).Contains #[] (normalized w)[slot]

/-- All ordinary positions on the same source list, including execute0 rows. -/
def Effects {R : Type} [Field R] (proofs : List (Airbender.NativeInitializationBatch.Proof R)) : Prop :=
  ∀ w ∈ Airbender.NativeTokenLedger.mainRows (Airbender.NativeInitializationBatch.mainProofs proofs), RuntimeRowEffects w
end Airbender.NativeCallerMixedQueries
