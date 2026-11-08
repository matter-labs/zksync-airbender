import Airbender.Proofs.ReducedMachine.NativeDelegationKeyAccounting

namespace Airbender.NativeDelegationKeyAccounting
open Airbender.NativeWorkerSnapshot Airbender.ReducedMachine.Native Airbender.Trace Airbender.Verification
open Airbender.Blake2Worker.Native Airbender.ReducedMachine.NativeMemoryBoundary

/-- SAME counted source/public image/log20/OLD logical boundaries derive unique
    active worker raw clock pairs and full delegation keys from actual x12 writes.
    Every raw-key aggregate over ALLcaller rows equals the exact 0/1 indicator
    of an active worker at that key. Nonzero aggregate iff a unique active worker
    key is present. No caller Booleanity/count/activity or expected matching premise.
    Individual nonzero rows may cancel; per-row caller validity/activity and
    issuance bijection are NOT established. The joint token execution remains.
    Physical round sequence/standard scheduled hash, original CSR/MOP/worker Sail,
    physical cryptography, completeness and parity remain open. -/
theorem native_counted_delegation_key_accounting {Setup R : Type} [Field R]
    (publicSetup : SparseDecoderSetup Airbender.NativeCallerDecoder.Mode)
    (embed : F →+* R) (memory : MemoryKeyChallenges R) (ch : CSRArgumentChallenges R)
    (pc : PCChallenges R) (gamma : R)
    (decoder : Airbender.ReducedMachine.NativeDecoderArguments.Challenges R) (config : WorkerConfiguration Setup)
    {batch : Airbender.NativeMainDecoder.Batch R} {workers : WorkerBatch Setup R}
    {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : Airbender.NativeMainDecoder.SourceAccepted publicSetup embed memory ch pc gamma decoder config batch workers inputs inverse)
    {before : Reference.RiscV.Sail.State} {count : Nat}
    (image : Airbender.NativeCallerDecoder.setupImage before count 20 = some publicSetup)
    (lookups : Airbender.NativeMainDecoder.LogicalLookups publicSetup batch)
    (identity : Airbender.NativeDelegationSupport.SourceIdentity batch.main.proofs workers) : Airbender.NativeDelegationKeyAccounting.Effects batch workers inputs :=
  NativeDelegationKeyAccountingProofs.counted publicSetup embed memory ch pc gamma decoder config accepted image lookups identity
end Airbender.NativeDelegationKeyAccounting
