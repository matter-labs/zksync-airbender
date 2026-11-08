import Airbender.Review.Trace.Families.ReducedMachine.WorkerSnapshot

namespace Airbender.NativeWorkerGroup
open Airbender.NativeWorkerSnapshot Airbender.Blake2Worker.Native Airbender.ReducedMachine.NativeMemoryBoundary
abbrev ports (w : Nat → F) := Airbender.NativeMemoryRoots.workerSteps w

/-- Actual writable ABI outputs decoded from post-state token samples. -/
def sampledOutput (samples : Fin 43 → Token) : Airbender.NativeWorkerTransition.Output :=
  ⟨(fun word => Airbender.NativeWorkerFirstG.pack
      (Airbender.NativeMemoryTokens.decodeKey (samples ⟨1+word.val,by have := word.isLt; omega⟩)).value[(0 : Fin 2)]
      (Airbender.NativeMemoryTokens.decodeKey (samples ⟨1+word.val,by have := word.isLt; omega⟩)).value[(1 : Fin 2)]),
   (fun word => Airbender.NativeWorkerFirstG.pack
      (Airbender.NativeMemoryTokens.decodeKey (samples ⟨9+word.val,by have := word.isLt; omega⟩)).value[(0 : Fin 2)]
      (Airbender.NativeMemoryTokens.decodeKey (samples ⟨9+word.val,by have := word.isLt; omega⟩)).value[(1 : Fin 2)]),
   (Airbender.NativeMemoryTokens.decodeKey (samples 42)).value[(0 : Fin 2)].val,
   (Airbender.NativeMemoryTokens.decodeKey (samples 42)).value[(1 : Fin 2)].val⟩

/-- A contiguous derived worker block in a complete raw-token replay. Every
    other edge occurrence remains in the prior or residual list, including
    other-address writes with equal proof ranks. This is not a physical schedule. -/
def Segment {Setup R : Type} [Field R]
    (proofs : List (Airbender.NativeInitializationBatch.Proof R)) (workers : WorkerBatch Setup R)
    (inputs : PublicBoundary) (w : Nat → F) (before after : List Token) : Prop :=
  ∃ prior rest : List (Token × Token),
    (prior ++ ports w ++ rest).Perm (Airbender.NativeMemoryRoots.steps proofs workers) ∧
    Airbender.NativeMixedReplay.Replay Trace.MemoryToken.address
      (Airbender.NativeInitializationSeedBoundary.initialTokens proofs) prior before ∧
    Airbender.NativeMixedReplay.Replay Trace.MemoryToken.address before (ports w) after ∧
    Airbender.NativeMixedReplay.Replay Trace.MemoryToken.address after rest
      (Airbender.NativeInitializationSeedBoundary.terminalTokens proofs inputs) ∧
    (∀ edge ∈ prior, Airbender.NativeCompleteMemoryPaths.rank edge.2 < Airbender.NativeCompleteMemoryPaths.rank (write w 0)) ∧
    rest.Pairwise (fun a b => Airbender.NativeCompleteMemoryPaths.rank a.2 ≤ Airbender.NativeCompleteMemoryPaths.rank b.2) ∧
    (∀ edge ∈ rest, Airbender.NativeCompleteMemoryPaths.rank (write w 0) ≤ Airbender.NativeCompleteMemoryPaths.rank edge.2)

/-- Exact post-state and unaffected-address frame of ALL43 actual ports.
    Prior snapshot samples supply the complete weighted reference inputs;
    ALL25writable results and ALL18readonly refreshes remain in this block. -/
structure RowEffects {Setup R : Type} [Field R]
    (proofs : List (Airbender.NativeInitializationBatch.Proof R)) (workers : WorkerBatch Setup R)
    (inputs : PublicBoundary) (w : Nat → F) (before after : List Token) : Prop where
  snapshot : AtSnapshot proofs workers inputs w before
  segment : Segment proofs workers inputs w before after
  unique : (after.map Trace.MemoryToken.address).Nodup
  writes : ∀ slot, write w slot ∈ after
  exact : ∀ slot token, token ∈ after → token.address = (write w slot).address → token = write w slot
  frame : ∀ token, (∀ slot, token.address ≠ (write w slot).address) → (token ∈ after ↔ token ∈ before)
  reference : ∀ old fresh : Fin 43 → Token,
    (∀ slot, old slot ∈ before ∧ (old slot).address = (read w slot).address) →
    (∀ slot, fresh slot ∈ after ∧ (fresh slot).address = (write w slot).address) →
    sampledOutput fresh = Airbender.NativeWorkerTransition.transition (sampledInput old)
  readonly : ∀ slot, (memoryAccess slot).writeValue = none → (write w slot).value = (read w slot).value

structure Effects {Setup R : Type} [Field R]
    (batch : Airbender.NativeMainDecoder.Batch R) (workers : WorkerBatch Setup R) (inputs : PublicBoundary) : Prop where
  prior : Airbender.NativeWorkerSnapshot.Effects batch workers inputs
  workers : ∀ w ∈ Airbender.NativeTokenLedger.workerRows workers, w constraintsABI.multiplicity = 1 →
    ∃ before after, RowEffects batch.main.proofs workers inputs w before after
end Airbender.NativeWorkerGroup
