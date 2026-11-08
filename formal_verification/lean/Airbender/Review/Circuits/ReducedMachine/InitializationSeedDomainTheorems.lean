import Airbender.Proofs.ReducedMachine.NativeInitializationSeedDomain

namespace Airbender.NativeInitializationSeedDomain
open Airbender.NativeInitializationLedger (F)
open Airbender.NativeInitializationBatch (Proof mainProofs)
open Airbender.ReducedMachine.Native Airbender.ReducedMachine.NativeMainAuxiliary
open Airbender.ReducedMachine.NativeMemoryBoundary Airbender.Blake2Worker.Native

/-- Unique actual observed RAM seeds on SAME accepted native proof list, exactly
    encoding canonical zero cells. Independent public-domain/Sail-read coverage,
    shadow/architectural separation, alignment and combined history remain open. -/
theorem native_observed_seed_domain {Setup R : Type} [Field R] (embed : F →+* R) (memory : MemoryKeyChallenges R)
    (ch : CSRArgumentChallenges R) (pc : PCChallenges R) (gamma : R) (config : WorkerConfiguration Setup)
    {proofs : List (Proof R)} {batch : WorkerBatch Setup R} {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : Airbender.NativeInitializationBatch.Accepted embed memory ch pc gamma config proofs batch inputs inverse) :
    Effects proofs :=
  NativeInitializationSeedDomainProofs.seed_domains embed memory ch pc gamma config accepted

/-- Constructed observed seed/teardown projection has exact original full native
    logical matching, with all public and worker access observations retained. -/
theorem native_observed_seed_ledger {Setup R : Type} [Field R] (proofs : List (Proof R))
    (batch : WorkerBatch Setup R) (inputs : PublicBoundary) :
    Airbender.NativeTokenLedger.LogicalMatching (mainProofs proofs) batch inputs ↔
      ((tokens proofs true).map Airbender.NativeTokenLedger.Token.memory ++
        Airbender.NativeInitializationLedger.accessTokens (mainProofs proofs) batch inputs true).Perm
      ((tokens proofs false).map Airbender.NativeTokenLedger.Token.memory ++
        Airbender.NativeInitializationLedger.accessTokens (mainProofs proofs) batch inputs false) :=
  NativeInitializationSeedDomainProofs.matching proofs batch inputs
end Airbender.NativeInitializationSeedDomain
