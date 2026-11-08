import Airbender.Review.Circuits.ReducedMachine.DelegationSupport
import Airbender.Review.Circuits.ReducedMachine.WorkerClockProgress

namespace Airbender.NativeWorkerSignedClocks
open Airbender.Blake2Worker.Native
abbrev F := ZMod mersenne31Modulus

/-- Proof ordering only: interpret the exact FIELD sentinel as integer-1.
    This does not change a token, its raw limbs, or native/Sail execution. -/
def limb (raw : F) : Int := if raw = -1 then -1 else (raw.val : Int)

def value (raw : F × F) : Int := limb raw.1 + 524288*limb raw.2

def workerValue (w : Nat → F) : Int := value (Airbender.NativeActiveWorkerClocks.workerClock w)

def readValue (w : Nat → F) (slot : Fin 43) : Int :=
  value (Airbender.NativeWorkerClockProgress.readToken w slot).time

/-- Derived ordering on SAME actual observations; every raw clock/token stays.
    Strict progress is not canonical19bit range, caller activity, initialized
    seed reachability, uniqueness, STAGE2 key refinement or worker Sail effects. -/
structure Effects {Setup R : Type} [Field R]
    (proofs : List (Airbender.NativeInitializationBatch.Proof R)) (batch : WorkerBatch Setup R) : Prop where
  reads : ∀ token ∈ Airbender.NativeInitializationSeedBoundary.accessTokens proofs batch false, 0 ≤ value token.time
  workers : ∀ w ∈ Airbender.NativeTokenLedger.workerRows batch, w constraintsABI.multiplicity = 1 → 0 < workerValue w
  progress : ∀ w ∈ Airbender.NativeTokenLedger.workerRows batch, w constraintsABI.multiplicity = 1 →
    ∀ slot : Fin 43, readValue w slot < workerValue w
  zero : ∀ w ∈ Airbender.NativeTokenLedger.workerRows batch, w constraintsABI.multiplicity = 1 →
    Airbender.NativeActiveWorkerClocks.workerClock w ≠ (0,0)
/-- An observed exact full-token worker-to-worker dependency, including both
    raw timestamp fields, address and value. No expected source is supplied. -/
def Dependency {Setup R : Type} [Field R] (batch : WorkerBatch Setup R)
    (writer reader : Nat → F) : Prop :=
  writer ∈ Airbender.NativeTokenLedger.workerRows batch ∧
    reader ∈ Airbender.NativeTokenLedger.workerRows batch ∧
    writer constraintsABI.multiplicity = 1 ∧ reader constraintsABI.multiplicity = 1 ∧
    ∃ writeSlot readSlot : Fin 43,
      Airbender.NativeMemoryTokens.encodeKey (quotientMemoryKey writer writeSlot true) =
        Airbender.NativeWorkerClockProgress.readToken reader readSlot

def NoWorkerCycles {Setup R : Type} [Field R] (batch : WorkerBatch Setup R) : Prop :=
  ∀ w, ¬ Relation.TransGen (Dependency batch) w w
end Airbender.NativeWorkerSignedClocks
