import Airbender.Review.Circuits.ReducedMachine.MixedMemoryOrder

namespace Airbender.NativeMemoryRoots
open Airbender.Blake2Worker.Native
abbrev F := ZMod mersenne31Modulus
abbrev Token := Trace.MemoryToken mersenne31Modulus

def workerSteps (w : Nat → F) : List (Token × Token) :=
  (List.finRange 43).map fun slot =>
    (Airbender.NativeWorkerClockProgress.readToken w slot,
      Airbender.NativeMemoryTokens.encodeKey (quotientMemoryKey w slot true))

/-- Actual active edges, preserving all positions, aliases and readonly refreshes.
    Inactive worker accesses remain in full acceptance; their exact equal read
    and write tokens are cancelled only in a derived logical memory ledger. -/
def steps {Setup R : Type} [Field R]
    (proofs : List (Airbender.NativeInitializationBatch.Proof R)) (batch : WorkerBatch Setup R) :=
  (Airbender.NativeMixedMemoryOrder.mainRows proofs).flatMap Trace.Row.memorySteps ++
    (Airbender.NativeTokenLedger.workerRows batch).flatMap fun w =>
      if w constraintsABI.multiplicity = 1 then workerSteps w else []

def tokens {Setup R : Type} [Field R]
    (proofs : List (Airbender.NativeInitializationBatch.Proof R)) (batch : WorkerBatch Setup R) (write : Bool) :=
  (steps proofs batch).map (if write then Prod.snd else Prod.fst)

/-- Common inactive worker observations, including positional duplicates.
    No auxiliary value, pole, source equation or physical row is removed. -/
def inactiveTokens {Setup R : Type} [Field R] (batch : WorkerBatch Setup R) :=
  (Airbender.NativeTokenLedger.workerRows batch).flatMap fun w =>
    if w constraintsABI.multiplicity = 1 then [] else Airbender.NativeMemoryTokens.workerTokens w false

/-- Exact raw-token paths from actual public seeds. The noninjective signed
    clock is used only for well-founded induction, never as token encoding.
    This does not establish unique/latest reads, an online history, canonical
    clock limbs, STAGE2 addresses, worker reference results or Sail execution. -/
structure Effects {Setup R : Type} [Field R]
    (proofs : List (Airbender.NativeInitializationBatch.Proof R)) (batch : WorkerBatch Setup R)
    (inputs : Airbender.ReducedMachine.NativeMemoryBoundary.PublicBoundary) : Prop where
  order : Airbender.NativeMixedMemoryOrder.Effects proofs batch
  partition : ∀ write, (Airbender.NativeInitializationSeedBoundary.accessTokens proofs batch write).Perm
    (tokens proofs batch write ++ inactiveTokens batch)
  matching : (Airbender.NativeInitializationSeedBoundary.initialTokens proofs ++ tokens proofs batch true).Perm
    (Airbender.NativeInitializationSeedBoundary.terminalTokens proofs inputs ++ tokens proofs batch false)
  reads : ∀ read write, Airbender.NativeMixedMemoryOrder.Step proofs batch read write →
    ∃ seed ∈ Airbender.NativeInitializationSeedBoundary.initialTokens proofs,
      Relation.ReflTransGen (Airbender.NativeMixedMemoryOrder.Step proofs batch) seed read
  writes : ∀ read write, Airbender.NativeMixedMemoryOrder.Step proofs batch read write →
    ∃ seed ∈ Airbender.NativeInitializationSeedBoundary.initialTokens proofs,
      Relation.ReflTransGen (Airbender.NativeMixedMemoryOrder.Step proofs batch) seed write
end Airbender.NativeMemoryRoots
