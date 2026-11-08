import Airbender.Review.Trace.Families.ReducedMachine.MixedReplayTheorems
import Tests.NativeMixedWordBounds

namespace Airbender.Tests.NativeMixedReplay
open Airbender.NativeMixedReplay Airbender.NativeMixedReplayProofs
open Airbender.Trace Airbender.ReducedMachine.Native Airbender.Verification
open Airbender.Blake2Worker.Native Airbender.ReducedMachine.NativeMemoryBoundary
private abbrev F := ZMod mersenne31Modulus
private abbrev T := Nat × Nat × Nat
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

/-- Pure changing-value chain, not a native/global accepted witness. -/
theorem changing_values : Replay (Prod.fst : T → Nat)
    [(0,0,0)] [((0,0,0),(0,1,9)),((0,1,9),(0,2,11))] [(0,2,11)] := by
  apply replay_sorted Prod.fst (fun token : T => token.2.1)
  · decide +kernel
  · decide +kernel
  · intro edge member
    simp only [List.mem_cons,List.mem_nil_iff,or_false] at member
    rcases member with rfl | rfl <;> decide +kernel
  · intro edge member
    simp only [List.mem_cons,List.mem_nil_iff,or_false] at member
    rcases member with rfl | rfl <;> decide +kernel
  · decide +kernel

/-- Different addresses may share a write rank. No injective clock is needed. -/
theorem simultaneous_forward : Replay (Prod.fst : T → Nat)
    [(0,0,0),(1,0,0)] [((0,0,0),(0,1,9)),((1,0,0),(1,1,11))] [(0,1,9),(1,1,11)] := by
  apply replay_sorted Prod.fst (fun token : T => token.2.1)
  · decide +kernel
  · decide +kernel
  · intro edge member
    simp only [List.mem_cons,List.mem_nil_iff,or_false] at member
    rcases member with rfl | rfl <;> decide +kernel
  · intro edge member
    simp only [List.mem_cons,List.mem_nil_iff,or_false] at member
    rcases member with rfl | rfl <;> decide +kernel
  · decide +kernel

theorem simultaneous_reverse : Replay (Prod.fst : T → Nat)
    [(0,0,0),(1,0,0)] [((1,0,0),(1,1,11)),((0,0,0),(0,1,9))] [(0,1,9),(1,1,11)] := by
  apply replay_sorted Prod.fst (fun token : T => token.2.1)
  · decide +kernel
  · decide +kernel
  · intro edge member
    simp only [List.mem_cons,List.mem_nil_iff,or_false] at member
    rcases member with rfl | rfl <;> decide +kernel
  · intro edge member
    simp only [List.mem_cons,List.mem_nil_iff,or_false] at member
    rcases member with rfl | rfl <;> decide +kernel
  · decide +kernel

theorem wrong_read_rejected : ¬ Replay (Prod.fst : T → Nat)
    [(0,0,0)] [((0,0,9),(0,1,11))] [(0,1,11)] := by
  intro run
  have wrong := head_read Prod.fst run (candidate := (0,0,0)) (by simp) rfl
  exact (by decide : (0,0,0) ≠ (0,0,9)) wrong

theorem duplicate_addresses_rejected : ¬ Replay (Prod.fst : T → Nat)
    [(0,0,0),(0,0,9)] [] [(0,0,0),(0,0,9)] := by
  intro run
  have distinct := initial_unique Prod.fst run
  exact (by decide : ¬ ([0,0] : List Nat).Nodup) distinct

/-- The read conclusion identifies BOTH raw timestamp fields and the value. -/
theorem raw_token_read {state terminal : List (MemoryToken mersenne31Modulus)}
    {read write candidate : MemoryToken mersenne31Modulus} {edges : List (_ × _)}
    (run : Replay MemoryToken.address state ((read,write) :: edges) terminal)
    (member : candidate ∈ state) (same : candidate.address = read.address) :
    candidate.time = read.time ∧ candidate.value = read.value := by
  have exactToken := head_read MemoryToken.address run member same
  exact ⟨congrArg MemoryToken.time exactToken,congrArg MemoryToken.value exactToken⟩

theorem all_active_ports {Setup R : Type} [Field R]
    {batch : Airbender.NativeMainDecoder.Batch R} {workers : WorkerBatch Setup R} {inputs : PublicBoundary}
    (effects : Effects batch workers inputs) :
    ∃ ordered : List (MemoryToken mersenne31Modulus × MemoryToken mersenne31Modulus), ordered.Perm (Airbender.NativeMemoryRoots.steps batch.main.proofs workers) ∧
      ∀ read write, Airbender.NativeMixedMemoryOrder.Step batch.main.proofs workers read write →
        (read,write) ∈ ordered := by
  obtain ⟨ordered,permutation,_,_⟩ := effects.replay
  exact ⟨ordered,permutation,fun read write actual => permutation.mem_iff.mpr
    ((Airbender.NativeMemoryRootsProofs.step_iff batch.main.proofs workers read write).mpr actual)⟩

theorem worker43_ports {Setup R : Type} [Field R]
    {batch : Airbender.NativeMainDecoder.Batch R} {workers : WorkerBatch Setup R} {inputs : PublicBoundary}
    (effects : Effects batch workers inputs) {w : Nat → F} (member : w ∈ Airbender.NativeTokenLedger.workerRows workers)
    (active : w constraintsABI.multiplicity = 1) :
    ∃ ordered : List (MemoryToken mersenne31Modulus × MemoryToken mersenne31Modulus), ordered.Perm (Airbender.NativeMemoryRoots.steps batch.main.proofs workers) ∧
      ∀ slot : Fin 43, (Airbender.NativeWorkerClockProgress.readToken w slot,
        Airbender.NativeMemoryTokens.encodeKey (quotientMemoryKey w slot true)) ∈ ordered := by
  obtain ⟨ordered,permutation,ports⟩ := all_active_ports effects
  exact ⟨ordered,permutation,fun slot => ports _ _ (Or.inr ⟨w,member,active,slot,rfl,rfl⟩)⟩

theorem word_bounds_retained {Setup R : Type} [Field R]
    {batch : Airbender.NativeMainDecoder.Batch R} {workers : WorkerBatch Setup R} {inputs : PublicBoundary}
    (effects : Effects batch workers inputs) : Airbender.NativeMixedWordBounds.Effects batch workers inputs := effects.words

theorem inactive_requests_retained :
    (Airbender.Tests.NativeCSRPositive.nativeRow false).assignment importedConstraintsTraceColumns.execute = 0 ∧
      csrRequest (Airbender.Tests.NativeCSRPositive.nativeRow false).assignment = ⟨1,1991,some 0,3⟩ :=
  Airbender.Tests.NativeMixedWordBounds.inactive_requests_retained

theorem complete_source {Setup R : Type} [Field R] (embed : F →+* R) (memory : MemoryKeyChallenges R)
    (ch : CSRArgumentChallenges R) (pc : PCChallenges R) (gamma : R) (config : WorkerConfiguration Setup)
    {proofs : List (Airbender.NativeInitializationBatch.Proof R)} {workers : WorkerBatch Setup R}
    {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : Airbender.NativeInitializationBatch.Accepted embed memory ch pc gamma config proofs workers inputs inverse)
    (identity : Airbender.NativeDelegationSupport.SourceIdentity proofs workers) : Execution proofs workers inputs :=
  native_memory_token_replay embed memory ch pc gamma config accepted identity

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
  native_counted_mixed_memory_replay publicSetup embed memory ch pc gamma decoder config accepted image lookups identity
end Airbender.Tests.NativeMixedReplay
