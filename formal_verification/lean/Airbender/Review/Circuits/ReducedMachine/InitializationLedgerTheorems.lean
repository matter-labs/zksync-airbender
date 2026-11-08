import Airbender.Proofs.ReducedMachine.NativeInitializationLedger

namespace Airbender.NativeInitializationLedger
open Airbender.ReducedMachine.Native Airbender.ReducedMachine.NativeMainAuxiliary
open Airbender.ReducedMachine.NativeMemoryBoundary Airbender.Blake2Worker.Native

/-- SAME accepted native main list: actual initialization tokens are canonical
    two-limb RAM32 zero seeds. This does not establish public image/seed coverage,
    an architectural RAM region, initialized worker reads or physical extraction. -/
theorem native_initialization_seed_domain {Setup R : Type} [Field R] (embed : F →+* R) (memory : MemoryKeyChallenges R)
    (ch : CSRArgumentChallenges R) (pc : PCChallenges R) (gamma : R) (config : WorkerConfiguration Setup)
    {proofs : List (Airbender.NativeInitializationBatch.Proof R)} {batch : WorkerBatch Setup R}
    {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : Airbender.NativeInitializationBatch.Accepted embed memory ch pc gamma config proofs batch inputs inverse)
    {proof : Airbender.NativeInitializationBatch.Proof R} (member : proof ∈ proofs)
    (i : Nat) (ordinary : i < scalar16Layout.traceLength-1) :
    ZeroSeed (initializationToken (proof.main.memory.rows i) true) ∧
      RAM32 (initializationToken (proof.main.memory.rows i) false) ∧
      addressValue (initializationToken (proof.main.memory.rows i) true) =
        Airbender.NativeInitializationSorted.addressValue (proof.main.memory.rows i) ∧
      addressValue (initializationToken (proof.main.memory.rows i) true) < 4294967296 :=
  NativeInitializationLedgerProofs.accepted_domains embed memory ch pc gamma config accepted member i ordinary

/-- Exact logical cancellation of identical padding and inactive contributions
    in BOTH directions, retaining public registers/PC and every worker port. -/
theorem native_initialization_padding_matching {Setup R : Type} [Field R] (mains : List (MainProof R))
    (batch : WorkerBatch Setup R) (inputs : PublicBoundary) :
    Airbender.NativeTokenLedger.LogicalMatching mains batch inputs ↔
      (retainedTokens mains batch inputs true).Perm (retainedTokens mains batch inputs false) :=
  NativeInitializationLedgerProofs.matching_iff mains batch inputs

/-- Explicit actual nonpadding seed/teardown and access ledgers, with exact
    logical matching equivalent to the SAME original full native ledger. -/
theorem native_seed_access_ledger {Setup R : Type} [Field R] (mains : List (MainProof R))
    (batch : WorkerBatch Setup R) (inputs : PublicBoundary) :
    Airbender.NativeTokenLedger.LogicalMatching mains batch inputs ↔
      (initializationTokens mains true ++ accessTokens mains batch inputs true).Perm
        (initializationTokens mains false ++ accessTokens mains batch inputs false) :=
  NativeInitializationLedgerProofs.seed_access_matching mains batch inputs
end Airbender.NativeInitializationLedger
