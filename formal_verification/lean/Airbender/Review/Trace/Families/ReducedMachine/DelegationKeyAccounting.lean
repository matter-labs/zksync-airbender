import Airbender.Review.Trace.Families.ReducedMachine.JointReplay

namespace Airbender.NativeDelegationKeyAccounting
open Airbender.NativeDelegationSupport Airbender.Blake2Worker.Native Airbender.ReducedMachine.NativeMemoryBoundary
/-- An observable sublist only; all inactive source rows/AUX/poles remain accepted. -/
def activeRows {Setup R : Type} [Field R] (workers : WorkerBatch Setup R) :=
  (Airbender.NativeTokenLedger.workerRows workers).filter fun w => w constraintsABI.multiplicity = 1

def keys {Setup R : Type} [Field R] (workers : WorkerBatch Setup R) := (activeRows workers).map workerKey

def callerWeight {R : Type} [Field R] (proofs : List (Airbender.NativeInitializationBatch.Proof R)) (target : Key) :=
  weightAt (callerRows proofs) callerKey (fun w => w 92) target

def workerWeight {Setup R : Type} [Field R] (workers : WorkerBatch Setup R) (target : Key) :=
  weightAt (Airbender.NativeTokenLedger.workerRows workers) workerKey (fun w => w constraintsABI.multiplicity) target

/-- Aggregate accounting on every raw four-field key, not per-row caller
    Booleanity/activity or a caller-position bijection. All caller weights remain. -/
structure Effects {Setup R : Type} [Field R]
    (batch : Airbender.NativeMainDecoder.Batch R) (workers : WorkerBatch Setup R) (inputs : PublicBoundary) : Prop where
  prior : Airbender.NativeJointReplay.Effects batch workers inputs
  clocksUnique : ((activeRows workers).map Airbender.NativeActiveWorkerClocks.workerClock).Nodup
  keysUnique : (keys workers).Nodup
  workerCoefficients : ∀ target, workerWeight workers target = if target ∈ keys workers then 1 else 0
  callerCoefficients : ∀ target, callerWeight batch.main.proofs target = if target ∈ keys workers then 1 else 0
  aggregateBoolean : ∀ target, callerWeight batch.main.proofs target = 0 ∨ callerWeight batch.main.proofs target = 1
  converse : ∀ target, callerWeight batch.main.proofs target ≠ 0 ↔ target ∈ keys workers
  uniqueWorker : ∀ a ∈ activeRows workers, ∀ b ∈ activeRows workers, workerKey a = workerKey b → a = b
end Airbender.NativeDelegationKeyAccounting
