import Airbender.Proofs.ReducedMachine.NativeMainDependencies

namespace Airbender.NativeMainDependencies
open Airbender.ReducedMachine.Native Airbender.Blake2Worker.Native
open Airbender.ReducedMachine.NativeMemoryBoundary Verification

/-- Full BODY derives both readonly value copies and the native SW-mask store
    value copy. No expected read, row mask or initialized word bound is supplied. -/
theorem native_main_value_dependencies {setup : Table F (fields 4)} {w : Nat → F}
    (accepted : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup)) : LocalEffects w :=
  NativeMainDependencyProofs.local_effects accepted

/-- Same complete counted source and prior worker/latest-read effects. Every
    actual read precedes all writes at its own or a later port offset. -/
theorem native_counted_main_read_dependencies {Setup R : Type} [Field R]
    (embed : F →+* R) (memory : MemoryKeyChallenges R) (ch : CSRArgumentChallenges R)
    (pc : PCChallenges R) (gamma : R) (config : WorkerConfiguration Setup)
    {batch : Airbender.NativeMainBatch.Batch R} {workers : WorkerBatch Setup R}
    {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : Airbender.NativeMainBatch.SourceAccepted embed memory ch pc gamma config batch workers inputs inverse)
    (identity : Airbender.NativeDelegationSupport.SourceIdentity batch.proofs workers) :
    Airbender.NativeMainBatch.Effects batch ∧ Effects batch.proofs workers inputs :=
  NativeMainDependencyProofs.counted embed memory ch pc gamma config accepted identity
end Airbender.NativeMainDependencies
