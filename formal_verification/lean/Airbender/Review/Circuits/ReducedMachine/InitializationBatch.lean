import Airbender.Review.Circuits.ReducedMachine.InitializationWindow
import Airbender.Review.Circuits.ReducedMachine.TokenLedger
import Airbender.Review.Circuits.ReducedMachine.MainStateHistory

namespace Airbender.NativeInitializationBatch
open Airbender.ReducedMachine.Native Airbender.ReducedMachine.NativeMainAuxiliary
open Airbender.ReducedMachine.NativeMemoryBoundary Airbender.Blake2Worker.Native
abbrev F := ZMod mersenne31Modulus

/-- One ACTUAL main argument, enriched with separate source observations for the
    scalar family and public initialization endpoints. No second MainProof/rows/
    auxiliary trace or desired trace/ledger equality is supplied. -/
structure Proof (R : Type) [Field R] where
  main : Airbender.ReducedMachine.NativeMainArguments.Proof R
  base : Nat → BaseAuxiliaryColumn → F
  witness : Nat → Scalar16WitnessColumn → F
  setup : Nat → Scalar16SetupColumn → F
  scalarPolynomial : Polynomial R
  scalarOmega : R
  values : Airbender.NativeInitializationBoundary.PublicValues

def Proof.scalar {R : Type} [Field R] (proof : Proof R) : Airbender.NativeScalar16Arguments.Proof R :=
  ⟨⟨proof.main.memory,proof.base⟩,proof.witness,proof.setup,proof.scalarPolynomial,proof.scalarOmega⟩

def Proof.chunk {R : Type} [Field R] (proof : Proof R) : Airbender.NativeInitializationWindow.Chunk R :=
  ⟨proof.scalar,proof.values⟩

def mainArguments {R : Type} [Field R] (proofs : List (Proof R)) := proofs.map Proof.main

def mainProofs {R : Type} [Field R] (proofs : List (Proof R)) := proofs.map fun proof => proof.main.memory

def initializationToken {R : Type} [Field R] (proof : Proof R) (row : Nat) (write : Bool) :=
  Airbender.NativeMemoryTokens.encodeKey (initializationKey (proof.main.memory.rows row) write)

/-- Complete existing main/caller/worker/global components on the SAME actual
    proof list, plus complete initialization source components and ALL native
    windows. Full tagged-token LogicalMatching stays explicit on that SAME list.
    No expected rows/seed/request/worker ledger/result or count equality supplied.
    Rust ProofOutput/count/caps/transcript/crypto extraction is separately scoped. -/
structure Accepted {Setup R : Type} [Field R] (embed : F →+* R) (memory : MemoryKeyChallenges R)
    (ch : CSRArgumentChallenges R) (pc : PCChallenges R) (gamma : R) (config : WorkerConfiguration Setup)
    (proofs : List (Proof R)) (batch : WorkerBatch Setup R) (inputs : PublicBoundary) (inverse : BoundaryInverses R) : Prop where
  arguments : Airbender.ReducedMachine.NativeMainArguments.Accepted embed memory ch pc config (mainArguments proofs) batch inputs inverse
  initialization : ∀ proof ∈ proofs, Airbender.NativeInitializationBoundary.Accepted embed memory pc gamma proof.scalar proof.values
  windows : ∀ c (bound : c + 1 < proofs.length), Airbender.NativeInitializationWindow.WindowAccepted
    (proofs[c]'(by omega)).values (proofs[c + 1]'bound).values
  matching : Airbender.NativeTokenLedger.LogicalMatching (mainProofs proofs) batch inputs

/-- Derived actual initialization consequences on the SAME full native ledger.
    These do not identify zero tokens with public seeds or initialized reads. -/
structure InitializationEffects {R : Type} [Field R] (proofs : List (Proof R)) : Prop where
  bounds : ∀ proof ∈ proofs, ∀ i < scalar16Layout.traceLength-1,
    (Airbender.NativeInitializationOrdering.address (proof.main.memory.rows i))[0].val < 65536 ∧
      (Airbender.NativeInitializationOrdering.address (proof.main.memory.rows i))[1].val < 65536
  order : ∀ c d (less : c < d) (bound : d < proofs.length), ∀ i < scalar16Layout.traceLength-1, ∀ j < scalar16Layout.traceLength-1,
    Airbender.NativeInitializationSorted.addressValue ((proofs[c]'(by omega)).main.memory.rows i) ≤
      Airbender.NativeInitializationSorted.addressValue ((proofs[d]'bound).main.memory.rows j) ∧
    (¬ Airbender.NativeInitializationOrdering.PaddingRecord ((proofs[c]'(by omega)).main.memory.rows i) →
      Airbender.NativeInitializationSorted.addressValue ((proofs[c]'(by omega)).main.memory.rows i) <
        Airbender.NativeInitializationSorted.addressValue ((proofs[d]'bound).main.memory.rows j))
  unique : ∀ c d i j (cb : c < proofs.length) (db : d < proofs.length),
    i < scalar16Layout.traceLength-1 → j < scalar16Layout.traceLength-1 →
    ¬ Airbender.NativeInitializationOrdering.PaddingRecord ((proofs[c]'cb).main.memory.rows i) →
    ¬ Airbender.NativeInitializationOrdering.PaddingRecord ((proofs[d]'db).main.memory.rows j) →
    (initializationToken (proofs[c]'cb) i true).address = (initializationToken (proofs[d]'db) j true).address → c = d ∧ i = j

end Airbender.NativeInitializationBatch
