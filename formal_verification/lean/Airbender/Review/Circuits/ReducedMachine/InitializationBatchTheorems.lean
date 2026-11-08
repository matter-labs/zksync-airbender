import Airbender.Proofs.ReducedMachine.NativeInitializationBatch

namespace Airbender.NativeInitializationBatch
open Airbender.ReducedMachine.Native Airbender.ReducedMachine.NativeMainAuxiliary
open Airbender.ReducedMachine.NativeMemoryBoundary Airbender.Blake2Worker.Native

/-- Existing caller/worker balances, actual main-state chronology AND global
    initialization bounds/order/uniqueness on the SAME actual main proof list.
    Full logical matching remains explicit; no initialized seed/read or worker
    semantics/accounting result is supplied or inferred. -/
theorem native_same_main_initialization {Setup R : Type} [Field R] (embed : F →+* R) (memory : MemoryKeyChallenges R)
    (ch : CSRArgumentChallenges R) (pc : PCChallenges R) (gamma : R) (config : WorkerConfiguration Setup)
    {proofs : List (Proof R)} {batch : WorkerBatch Setup R} {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : Accepted embed memory ch pc gamma config proofs batch inputs inverse) :
    Airbender.ReducedMachine.NativeMainArguments.Effects embed memory pc (mainArguments proofs) batch inputs ∧
      Airbender.NativeMainStateHistory.Effects (mainProofs proofs) inputs ∧ InitializationEffects proofs :=
  NativeInitializationBatchProofs.joint_effects embed memory ch pc gamma config accepted

/-- Every actual ordinary initialization/teardown token is an unmasked member of
    that SAME complete native ledger, on BOTH sides. No execute/profile filtering
    or expected initialization stream/ledger equality is assumed. -/
theorem native_same_main_initialization_tokens {Setup R : Type} [Field R]
    (proofs : List (Proof R)) (batch : WorkerBatch Setup R) (inputs : PublicBoundary)
    {proof : Proof R} (member : proof ∈ proofs) (i : Nat) (ordinary : i < scalar16Layout.traceLength-1) (write : Bool) :
    Airbender.NativeTokenLedger.Token.memory (initializationToken proof i write) ∈
      Airbender.NativeTokenLedger.fullTokens (mainProofs proofs) batch inputs write :=
  NativeInitializationBatchProofs.token_in_full proofs batch inputs member i ordinary write
end Airbender.NativeInitializationBatch
