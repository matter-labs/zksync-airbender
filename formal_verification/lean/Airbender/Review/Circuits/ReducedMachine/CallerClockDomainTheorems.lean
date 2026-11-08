import Airbender.Proofs.ReducedMachine.NativeCallerClockDomain

namespace Airbender.NativeCallerClockDomain
open Airbender.Verification Airbender.ReducedMachine.Native
open Airbender.ReducedMachine.NativeMemoryBoundary Airbender.Blake2Worker.Native

/-- All raw carry/wrap alternatives follow from complete native BODY acceptance. -/
theorem native_caller_clock_domain {setup : Table F (fields 4)} {w : Nat → F}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup)) : RowEffects w :=
  NativeCallerClockDomainProofs.body holds

/-- Every ordinary physical caller row, without an execute or request filter. -/
theorem native_all_caller_clock_domains {Setup R : Type} [Field R] (embed : F →+* R) (memory : MemoryKeyChallenges R)
    (ch : CSRArgumentChallenges R) (pc : PCChallenges R) (gamma : R) (config : WorkerConfiguration Setup)
    {proofs : List (Airbender.NativeInitializationBatch.Proof R)} {batch : WorkerBatch Setup R}
    {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : Airbender.NativeInitializationBatch.Accepted embed memory ch pc gamma config proofs batch inputs inverse) : Effects proofs :=
  NativeCallerClockDomainProofs.all_rows embed memory ch pc gamma config accepted
end Airbender.NativeCallerClockDomain
