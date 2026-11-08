import Airbender.Review.Trace.Families.ReducedMachine.MixedWordBoundsTheorems
import Tests.NativeCSRPositive

namespace Airbender.Tests.NativeMixedWordBounds
open Airbender.Trace Airbender.ReducedMachine.Native Airbender.Verification
open Airbender.Blake2Worker.Native Airbender.ReducedMachine.NativeMemoryBoundary
open Airbender.NativeMixedWordBounds
private abbrev F := ZMod mersenne31Modulus
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

/-- Pure changing-value chain, not a fabricated native global witness. -/
theorem rank_chain_changes : ∀ token ∈ ([(0,0)] : List (Nat × Nat)) ++ [(1,9),(2,11)], token.2 < 65536 := by
  have closure := Airbender.NativeMixedWordBoundsProofs.rank_closed ([(0,0)] : List (Nat × Nat))
    [((0,0),(1,9)),((1,9),(2,11))] Prod.fst (fun token => token.2 < 65536) ?_ ?_
  · exact closure
  · intro token member
    have same : token = (0,0) := by simpa using member
    rw [same]
    decide +kernel
  · intro edge member _
    simp only [List.mem_cons,List.mem_nil_iff,or_false] at member
    rcases member with rfl | rfl <;> decide +kernel

/-- Exact copying alone does not bound a value; the initialized source matters. -/
theorem copy_is_not_bound :
    let token : MemoryToken mersenne31Modulus := ⟨0,(0,0),Nat.pair 65536 0⟩
    token.value = token.value ∧ ¬ token.word.Bounded := by
  simp [MemoryToken.word,Nat.unpair_pair,Arithmetic.Word.Bounded,Arithmetic.limbBase]

theorem seed_words {Setup R : Type} [Field R]
    {batch : Airbender.NativeMainDecoder.Batch R} {workers : WorkerBatch Setup R} {inputs : PublicBoundary}
    (effects : Effects batch workers inputs) :
    ∀ token ∈ Airbender.NativeInitializationSeedBoundary.initialTokens batch.main.proofs, token.word.Bounded := by
  intro token member
  exact effects.available token (List.mem_append_left _ member)

theorem active_reads {Setup R : Type} [Field R]
    {batch : Airbender.NativeMainDecoder.Batch R} {workers : WorkerBatch Setup R} {inputs : PublicBoundary}
    (effects : Effects batch workers inputs) {read write : MemoryToken mersenne31Modulus}
    (edge : Airbender.NativeMixedMemoryOrder.Step batch.main.proofs workers read write) : read.word.Bounded :=
  (effects.steps read write edge).1

theorem active_writes {Setup R : Type} [Field R]
    {batch : Airbender.NativeMainDecoder.Batch R} {workers : WorkerBatch Setup R} {inputs : PublicBoundary}
    (effects : Effects batch workers inputs) {read write : MemoryToken mersenne31Modulus}
    (edge : Airbender.NativeMixedMemoryOrder.Step batch.main.proofs workers read write) : write.word.Bounded :=
  (effects.steps read write edge).2

/-- Both flags cover all43 ports on EVERY ordinary worker, including m0. -/
theorem ordinary_worker_reads {Setup R : Type} [Field R]
    {batch : Airbender.NativeMainDecoder.Batch R} {workers : WorkerBatch Setup R} {inputs : PublicBoundary}
    (effects : Effects batch workers inputs) {w : Nat → F} (member : w ∈ Airbender.NativeTokenLedger.workerRows workers)
    (slot : Fin 43) : (Airbender.NativeWorkerClockProgress.readToken w slot).word.Bounded :=
  effects.workers w member slot false

theorem ordinary_worker_writes {Setup R : Type} [Field R]
    {batch : Airbender.NativeMainDecoder.Batch R} {workers : WorkerBatch Setup R} {inputs : PublicBoundary}
    (effects : Effects batch workers inputs) {w : Nat → F} (member : w ∈ Airbender.NativeTokenLedger.workerRows workers)
    (slot : Fin 43) : (Airbender.NativeMemoryTokens.encodeKey (quotientMemoryKey w slot true)).word.Bounded :=
  effects.workers w member slot true

theorem terminal_words {Setup R : Type} [Field R]
    {batch : Airbender.NativeMainDecoder.Batch R} {workers : WorkerBatch Setup R} {inputs : PublicBoundary}
    (effects : Effects batch workers inputs) :
    ∀ token ∈ Airbender.NativeInitializationSeedBoundary.terminalTokens batch.main.proofs inputs, token.word.Bounded :=
  effects.terminal

theorem latest_retained {Setup R : Type} [Field R]
    {batch : Airbender.NativeMainDecoder.Batch R} {workers : WorkerBatch Setup R} {inputs : PublicBoundary}
    (effects : Effects batch workers inputs) : Airbender.NativeLatestReads.Effects batch.main.proofs workers inputs :=
  effects.prior.workers.prior.latest

/-- The complete inactive local CSR request remains; no caller filter is added. -/
theorem inactive_requests_retained :
    (Airbender.Tests.NativeCSRPositive.nativeRow false).assignment importedConstraintsTraceColumns.execute = 0 ∧
      csrRequest (Airbender.Tests.NativeCSRPositive.nativeRow false).assignment = ⟨1,1991,some 0,3⟩ :=
  Airbender.Tests.NativeCSRPositive.inactive_body_still_requests.2

theorem complete_counted {Setup R : Type} [Field R]
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
    (identity : Airbender.NativeDelegationSupport.SourceIdentity batch.main.proofs workers) : Effects batch workers inputs :=
  native_initialized_mixed_words publicSetup embed memory ch pc gamma decoder config accepted image lookups identity
end Airbender.Tests.NativeMixedWordBounds
