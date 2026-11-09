import Airbender.Review.Trace.Families.ReducedMachine.CallerCount

namespace Airbender.NativeCallerPosition
open Airbender.NativeDelegationSupport

/-- Unique partners at ORIGINAL list indices, without changing either accepted
    source list. Equal row values at different positions remain distinct. -/
def IndexMatching {A B K : Type} (callers : List A) (workers : List B)
    (callerKey : A → K) (workerKey : B → K) (callerWeight : A → F) (workerWeight : B → F) : Prop :=
  (∀ i : Fin callers.length, callerWeight callers[i.val] = 1 →
    ∃! j : Fin workers.length, workerWeight workers[j.val] = 1 ∧ callerKey callers[i.val] = workerKey workers[j.val]) ∧
  (∀ j : Fin workers.length, workerWeight workers[j.val] = 1 →
    ∃! i : Fin callers.length, callerWeight callers[i.val] = 1 ∧ callerKey callers[i.val] = workerKey workers[j.val])

open Airbender.Blake2Worker.Native Airbender.ReducedMachine.NativeMemoryBoundary

def Matching {Setup R : Type} [Field R] (batch : Airbender.NativeMainDecoder.Batch R) (workers : WorkerBatch Setup R) : Prop :=
  IndexMatching (callerRows batch.main.proofs) (Airbender.NativeTokenLedger.workerRows workers)
    callerKey workerKey (fun w => w 92) (fun w => w constraintsABI.multiplicity)

/-- A derived source dichotomy; no small-count/activity/matching premise is added.
    Request-positive inactive callers remain included. Physical activity and the
    larger-batch characteristic ambiguity are still separate open connections. -/
structure Effects {Setup R : Type} [Field R]
    (batch : Airbender.NativeMainDecoder.Batch R) (workers : WorkerBatch Setup R) (inputs : PublicBoundary) : Prop where
  prior : Airbender.NativeCallerCount.Effects batch workers inputs
  matching_or_large : Matching batch workers ∨ 257 ≤ batch.countWord.toNat
end Airbender.NativeCallerPosition

