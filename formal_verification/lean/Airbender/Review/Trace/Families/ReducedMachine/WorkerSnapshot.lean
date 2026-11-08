import Airbender.Review.Trace.Families.ReducedMachine.MixedReplay
import Airbender.Review.Circuits.Blake2Worker.Transition

namespace Airbender.NativeWorkerSnapshot
open Airbender.Blake2Worker.Native Airbender.ReducedMachine.NativeMemoryBoundary
abbrev F := ZMod mersenne31Modulus
abbrev Token := Trace.MemoryToken mersenne31Modulus
abbrev read (w : Nat → F) (slot : Fin 43) := Airbender.NativeWorkerClockProgress.readToken w slot
abbrev write (w : Nat → F) (slot : Fin 43) := Airbender.NativeMemoryTokens.encodeKey (quotientMemoryKey w slot true)

/-- Reference inputs decoded from exact snapshot samples, with both x12 fields.
    This uses the old lossless raw-key decoder, not a clock or word recoding. -/
def sampledInput (samples : Fin 43 → Token) : Airbender.NativeWorkerTransition.Input :=
  ⟨(Airbender.NativeMemoryTokens.decodeKey (samples 42)).value[(0 : Fin 2)],
   (Airbender.NativeMemoryTokens.decodeKey (samples 42)).value[(1 : Fin 2)].val,
   (fun word limb => (Airbender.NativeMemoryTokens.decodeKey (samples ⟨1+word.val,by have := word.isLt; omega⟩)).value[limb]),
   (fun word limb => (Airbender.NativeMemoryTokens.decodeKey (samples ⟨9+word.val,by have := word.isLt; omega⟩)).value[limb]),
   (fun word limb => (Airbender.NativeMemoryTokens.decodeKey (samples ⟨26+word.val,by have := word.isLt; omega⟩)).value[limb])⟩

/-- A derived cut of the SAME complete replay, before every write at this rank.
    Ranks are noninjective proof order; both raw timestamp fields stay in tokens. -/
def Cut {Setup R : Type} [Field R]
    (proofs : List (Airbender.NativeInitializationBatch.Proof R)) (workers : WorkerBatch Setup R)
    (inputs : PublicBoundary) (time : Nat) (snapshot : List Token) : Prop :=
  ∃ prior suffix : List (Token × Token),
    (prior ++ suffix).Perm (Airbender.NativeMemoryRoots.steps proofs workers) ∧
    (prior ++ suffix).Pairwise (fun a b => Airbender.NativeCompleteMemoryPaths.rank a.2 ≤ Airbender.NativeCompleteMemoryPaths.rank b.2) ∧
    Airbender.NativeMixedReplay.Replay Trace.MemoryToken.address
      (Airbender.NativeInitializationSeedBoundary.initialTokens proofs) prior snapshot ∧
    Airbender.NativeMixedReplay.Replay Trace.MemoryToken.address snapshot suffix
      (Airbender.NativeInitializationSeedBoundary.terminalTokens proofs inputs) ∧
    (∀ edge ∈ prior, Airbender.NativeCompleteMemoryPaths.rank edge.2 < time) ∧
    (∀ edge ∈ suffix, time ≤ Airbender.NativeCompleteMemoryPaths.rank edge.2)

/-- Every port samples one common initialized pre-state. Exact tokens include
    address, value and BOTH raw times. The complete weighted reference result is
    attached to those reads. No physical round sequence or grouped post-state,
    standard scheduled hash or original Sail worker execution is asserted. -/
structure AtSnapshot {Setup R : Type} [Field R]
    (proofs : List (Airbender.NativeInitializationBatch.Proof R)) (workers : WorkerBatch Setup R)
    (inputs : PublicBoundary) (w : Nat → F) (snapshot : List Token) : Prop where
  cut : Cut proofs workers inputs (Airbender.NativeCompleteMemoryPaths.rank (write w 0)) snapshot
  unique : (snapshot.map Trace.MemoryToken.address).Nodup
  reads : ∀ slot, read w slot ∈ snapshot
  exact : ∀ slot token, token ∈ snapshot → token.address = (read w slot).address → token = read w slot
  addresses : Function.Injective (fun slot : Fin 43 => (write w slot).address)
  commonTime : ∀ slot, (write w slot).time = (write w 0).time
  sampled : ∀ samples : Fin 43 → Token,
    (∀ slot, samples slot ∈ snapshot ∧ (samples slot).address = (read w slot).address) →
    sampledInput samples = Airbender.NativeWorkerTransition.readInput w
  result : Airbender.NativeWorkerTransition.observed w =
    Airbender.NativeWorkerTransition.transition (Airbender.NativeWorkerTransition.readInput w)

structure Effects {Setup R : Type} [Field R]
    (batch : Airbender.NativeMainDecoder.Batch R) (workers : WorkerBatch Setup R) (inputs : PublicBoundary) : Prop where
  prior : Airbender.NativeMixedReplay.Effects batch workers inputs
  transitions : ∀ w ∈ Airbender.NativeTokenLedger.workerRows workers, Airbender.NativeWorkerTransition.RowEffects w
  snapshots : ∀ w ∈ Airbender.NativeTokenLedger.workerRows workers, w constraintsABI.multiplicity = 1 →
    ∃ snapshot, AtSnapshot batch.main.proofs workers inputs w snapshot
end Airbender.NativeWorkerSnapshot
