import Airbender.Proofs.ReducedMachine.NativeMixedMemoryOrder

namespace Airbender.NativeMixedMemoryOrder
open Airbender.ReducedMachine.Native Airbender.Blake2Worker.Native
open Airbender.ReducedMachine.NativeMemoryBoundary

/-- Every actual active main/worker memory edge strictly increases a proof
    ordering on exact raw tokens. Prior crypto boundaries remain explicit. -/
theorem native_mixed_memory_order {Setup R : Type} [Field R]
    (embed : F →+* R) (memory : MemoryKeyChallenges R) (ch : CSRArgumentChallenges R)
    (pc : PCChallenges R) (gamma : R) (config : WorkerConfiguration Setup)
    {proofs : List (Airbender.NativeInitializationBatch.Proof R)} {workers : WorkerBatch Setup R}
    {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : Airbender.NativeInitializationBatch.Accepted embed memory ch pc gamma config proofs workers inputs inverse)
    (identity : Airbender.NativeDelegationSupport.SourceIdentity proofs workers) : Effects proofs workers :=
  NativeMixedMemoryOrderProofs.effects embed memory ch pc gamma config accepted identity

/-- Count and all prior components stay. Active mixed cycles are excluded;
    inactive worker loops remain in the full ledger. Seed paths stay open. -/
theorem native_counted_mixed_memory_order {Setup R : Type} [Field R]
    (embed : F →+* R) (memory : MemoryKeyChallenges R) (ch : CSRArgumentChallenges R)
    (pc : PCChallenges R) (gamma : R) (config : WorkerConfiguration Setup)
    {batch : Airbender.NativeMainBatch.Batch R} {workers : WorkerBatch Setup R}
    {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : Airbender.NativeMainBatch.SourceAccepted embed memory ch pc gamma config batch workers inputs inverse)
    (identity : Airbender.NativeDelegationSupport.SourceIdentity batch.proofs workers) :
    Airbender.NativeMainBatch.Effects batch ∧ Effects batch.proofs workers :=
  NativeMixedMemoryOrderProofs.counted embed memory ch pc gamma config accepted identity
end Airbender.NativeMixedMemoryOrder
