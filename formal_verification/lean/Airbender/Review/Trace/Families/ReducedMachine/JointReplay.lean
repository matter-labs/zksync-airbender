import Airbender.Review.Trace.Families.ReducedMachine.WorkerGroup

namespace Airbender.NativeJointReplay
open Airbender.NativeWorkerSnapshot Airbender.Blake2Worker.Native Airbender.ReducedMachine.NativeMemoryBoundary
/-- One sequence of exact block executions. All reads of a block are already
    present together; MAIN ports are separate singleton blocks. -/
inductive BatchReplay {A K G : Type} (key : A → K) (edges : G → List (A × A)) :
    List A → List G → List A → Prop
  | done {state terminal} (run : Airbender.NativeMixedReplay.Replay key state [] terminal) :
      BatchReplay key edges state [] terminal
  | step {state post terminal group groups}
      (reads : ∀ edge ∈ edges group, edge.1 ∈ state)
      (block : Airbender.NativeMixedReplay.Replay key state (edges group) post)
      (next : BatchReplay key edges post groups terminal) :
      BatchReplay key edges state (group :: groups) terminal

/-- Actual source labels, retaining positional copies without deduplication. -/
inductive Group
  | main (edge : Token × Token)
  | worker (w : Nat → F)

def edges : Group → List (Token × Token)
  | .main edge => [edge]
  | .worker w => Airbender.NativeWorkerGroup.ports w

def time : Group → Nat
  | .main edge => Airbender.NativeCompleteMemoryPaths.rank edge.2
  | .worker w => Airbender.NativeCompleteMemoryPaths.rank (write w 0)

def groups {Setup R : Type} [Field R]
    (proofs : List (Airbender.NativeInitializationBatch.Proof R)) (workers : WorkerBatch Setup R) : List Group :=
  ((Airbender.NativeMixedMemoryOrder.mainRows proofs).flatMap Trace.Row.memorySteps).map Group.main ++
    (Airbender.NativeTokenLedger.workerRows workers).flatMap fun w =>
      if w constraintsABI.multiplicity = 1 then [.worker w] else []

/-- A worker occurrence inside the ONE shared block order. -/
def Occurrence (ordered : List Group) (initial terminal : List Token)
    (w : Nat → F) (before after : List Token) : Prop :=
  ∃ prior rest, ordered = prior ++ Group.worker w :: rest ∧
    BatchReplay Trace.MemoryToken.address edges initial prior before ∧
    Airbender.NativeMixedReplay.Replay Trace.MemoryToken.address before (edges (.worker w)) after ∧
    BatchReplay Trace.MemoryToken.address edges after rest terminal

/-- Actual input/output samples and frame at this occurrence's shared snapshots. -/
structure WorkerEffect (w : Nat → F) (before after : List Token) : Prop where
  reads : ∀ slot, read w slot ∈ before
  beforeUnique : (before.map Trace.MemoryToken.address).Nodup
  afterUnique : (after.map Trace.MemoryToken.address).Nodup
  writes : ∀ slot, write w slot ∈ after
  exact : ∀ slot token, token ∈ after → token.address = (write w slot).address → token = write w slot
  frame : ∀ token, (∀ slot, token.address ≠ (write w slot).address) → (token ∈ after ↔ token ∈ before)
  reference : ∀ old fresh : Fin 43 → Token,
    (∀ slot, old slot ∈ before ∧ (old slot).address = (read w slot).address) →
    (∀ slot, fresh slot ∈ after ∧ (fresh slot).address = (write w slot).address) →
    Airbender.NativeWorkerGroup.sampledOutput fresh = Airbender.NativeWorkerTransition.transition (sampledInput old)
  readonly : ∀ slot, (memoryAccess slot).writeValue = none → (write w slot).value = (read w slot).value

/-- A single derived order contains every actual MAIN singleton and every active
    ALL43-port worker block, from actual initialization through actual teardown.
    Proof rank allows ties and is not a physical clock or round schedule. -/
def Execution {Setup R : Type} [Field R]
    (proofs : List (Airbender.NativeInitializationBatch.Proof R)) (workers : WorkerBatch Setup R)
    (inputs : PublicBoundary) : Prop :=
  ∃ ordered : List Group, ordered.Perm (groups proofs workers) ∧
    ordered.Pairwise (fun a b => time a ≤ time b) ∧
    (ordered.flatMap edges).Perm (Airbender.NativeMemoryRoots.steps proofs workers) ∧
    BatchReplay Trace.MemoryToken.address edges
      (Airbender.NativeInitializationSeedBoundary.initialTokens proofs) ordered
      (Airbender.NativeInitializationSeedBoundary.terminalTokens proofs inputs) ∧
    ∀ w ∈ Airbender.NativeTokenLedger.workerRows workers, w constraintsABI.multiplicity = 1 →
      ∃ before after,
        Occurrence ordered (Airbender.NativeInitializationSeedBoundary.initialTokens proofs)
          (Airbender.NativeInitializationSeedBoundary.terminalTokens proofs inputs) w before after ∧
        WorkerEffect w before after

structure Effects {Setup R : Type} [Field R]
    (batch : Airbender.NativeMainDecoder.Batch R) (workers : WorkerBatch Setup R) (inputs : PublicBoundary) : Prop where
  prior : Airbender.NativeWorkerGroup.Effects batch workers inputs
  joint : Execution batch.main.proofs workers inputs
end Airbender.NativeJointReplay
