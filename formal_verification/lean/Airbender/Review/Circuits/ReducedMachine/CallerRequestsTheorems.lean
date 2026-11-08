import Airbender.Proofs.ReducedMachine.NativeCallerRequests

namespace Airbender.NativeCallerRequests
open Airbender.Verification Airbender.ReducedMachine.Native
open Airbender.ReducedMachine.NativeMemoryBoundary Airbender.Blake2Worker.Native

/-- Complete native request shape without an execute or CSR-profile premise. -/
theorem native_caller_request_shape {setup : Table F (fields 4)} {w : Nat → F}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup)) : RowEffects w :=
  NativeCallerRequestProofs.body holds

/-- All actual ordinary main rows remain, including execute0 requests/poles. -/
theorem native_all_caller_requests {Setup R : Type} [Field R] (embed : F →+* R) (memory : MemoryKeyChallenges R)
    (ch : CSRArgumentChallenges R) (pc : PCChallenges R) (gamma : R) (config : WorkerConfiguration Setup)
    {proofs : List (Airbender.NativeInitializationBatch.Proof R)} {batch : WorkerBatch Setup R}
    {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : Airbender.NativeInitializationBatch.Accepted embed memory ch pc gamma config proofs batch inputs inverse) : Effects proofs :=
  NativeCallerRequestProofs.all_rows embed memory ch pc gamma config accepted

/-- Derived clocks on the EXISTING active main-state projection. This does not
    identify all physical requests with active rows or assert worker issuance. -/
theorem native_active_main_caller_clocks {Setup R : Type} [Field R] (embed : F →+* R) (memory : MemoryKeyChallenges R)
    (ch : CSRArgumentChallenges R) (pc : PCChallenges R) (gamma : R) (config : WorkerConfiguration Setup)
    {proofs : List (Airbender.NativeInitializationBatch.Proof R)} {batch : WorkerBatch Setup R}
    {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : Airbender.NativeInitializationBatch.Accepted embed memory ch pc gamma config proofs batch inputs inverse) : ActiveClockEffects proofs inputs :=
  NativeCallerRequestProofs.active_clocks embed memory ch pc gamma config accepted
end Airbender.NativeCallerRequests
