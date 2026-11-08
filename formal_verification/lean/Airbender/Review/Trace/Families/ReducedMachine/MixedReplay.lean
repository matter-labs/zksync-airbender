import Airbender.Review.Trace.Families.ReducedMachine.MixedWordBounds

namespace Airbender.NativeMixedReplay
/-- Exact token snapshots. Each step consumes its exact old token and replaces
    only that address. Raw fields are never replaced by an enumeration clock. -/
inductive Replay {A K : Type} (key : A → K) : List A → List (A × A) → List A → Prop
  | done {state terminal} (unique : (state.map key).Nodup)
      (same : state.Perm terminal) : Replay key state [] terminal
  | step {state rest read write edges terminal}
      (unique : (state.map key).Nodup) (present : state.Perm (read :: rest))
      (address : key read = key write)
      (next : Replay key (write :: rest) edges terminal) :
      Replay key state ((read,write) :: edges) terminal
open Airbender.Blake2Worker.Native Airbender.ReducedMachine.NativeMemoryBoundary
open Airbender.ReducedMachine.Native Airbender.Trace Airbender.Verification
/-- A derived serialization of every active MAIN/WORKER port. Proof ranks allow
    ties at different addresses; every state token retains both raw timestamps.
    This does not assert a physical worker schedule or original Sail execution. -/
def Execution {Setup R : Type} [Field R]
    (proofs : List (Airbender.NativeInitializationBatch.Proof R)) (workers : WorkerBatch Setup R)
    (inputs : PublicBoundary) : Prop :=
  ∃ ordered : List (Airbender.NativeMixedMemoryOrder.Token × Airbender.NativeMixedMemoryOrder.Token),
    ordered.Perm (Airbender.NativeMemoryRoots.steps proofs workers) ∧
    ordered.Pairwise (fun a b => Airbender.NativeCompleteMemoryPaths.rank a.2 ≤ Airbender.NativeCompleteMemoryPaths.rank b.2) ∧
    Replay Trace.MemoryToken.address (Airbender.NativeInitializationSeedBoundary.initialTokens proofs)
      ordered (Airbender.NativeInitializationSeedBoundary.terminalTokens proofs inputs)

structure Effects {Setup R : Type} [Field R]
    (batch : Airbender.NativeMainDecoder.Batch R) (workers : WorkerBatch Setup R) (inputs : PublicBoundary) : Prop where
  words : Airbender.NativeMixedWordBounds.Effects batch workers inputs
  replay : Execution batch.main.proofs workers inputs
end Airbender.NativeMixedReplay
