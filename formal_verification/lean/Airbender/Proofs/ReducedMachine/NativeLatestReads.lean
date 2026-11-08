import Airbender.Review.Circuits.ReducedMachine.LatestReads
import Airbender.Proofs.ReducedMachine.NativeMemoryWriteUniqueness
import Airbender.Proofs.Trace.LatestReads

namespace Airbender.NativeLatestReadsProofs
open Airbender.NativeLatestReads
open Airbender.Blake2Worker.Native Airbender.ReducedMachine.Native Airbender.ReducedMachine.NativeMemoryBoundary
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

/-- Generic exact-token inclusion in a complete counted path, before native
    data. Initial key uniqueness handles seeds; write ports retain all copies. -/
theorem on_path {S K : Type} [DecidableEq K] (key : S → K)
    {initial : List S} {steps : List (S × S)} {source : S} {path : List S}
    (unique : (initial.map key).Nodup) (seed : source ∈ initial)
    (first : path.head? = some source)
    (ports : (path.zip path.tail).Perm (steps.filter fun edge => key edge.1 = key source))
    (preserved : ∀ edge ∈ steps, key edge.1 = key edge.2)
    {candidate : S} (member : candidate ∈ initial ++ steps.map Prod.snd)
    (same : key candidate = key source) : candidate ∈ path := by
  rcases List.mem_append.mp member with initial | written
  · have equal := List.inj_on_of_nodup_map unique initial seed same
    rw [equal]
    exact List.mem_of_head? first
  · obtain ⟨edge,present,rfl⟩ := List.mem_map.mp written
    have selected : edge ∈ steps.filter (fun edge => key edge.1 = key source) :=
      List.mem_filter.mpr ⟨present,by simpa [preserved edge present] using same⟩
    exact List.mem_of_mem_tail (List.of_mem_zip (ports.mem_iff.mpr selected)).2

/-- Unchanged generic no-gap lemma plus exact rank injectivity on the path. -/
theorem path_latest {S : Type} (rank : S → Nat) {path : List S} {edge : S × S}
    (ordered : (path.map rank).Pairwise (· < ·)) (distinct : (path.map rank).Nodup)
    (port : edge ∈ path.zip path.tail) {candidate : S} (member : candidate ∈ path) :
    (rank candidate < rank edge.2 → rank candidate ≤ rank edge.1) ∧
    (rank candidate = rank edge.1 → candidate = edge.1) := by
  constructor
  · intro earlier
    have noGap := Airbender.Trace.Proofs.consecutive_ranks rank (List.pairwise_map.mp ordered) port member
    omega
  · intro same
    exact List.inj_on_of_nodup_map distinct member (List.of_mem_zip port).1 same

theorem effects {Setup R : Type} [Field R] (embed : F →+* R) (memory : MemoryKeyChallenges R)
    (ch : CSRArgumentChallenges R) (pc : PCChallenges R) (gamma : R) (config : WorkerConfiguration Setup)
    {proofs : List (Airbender.NativeInitializationBatch.Proof R)} {batch : WorkerBatch Setup R}
    {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : Airbender.NativeInitializationBatch.Accepted embed memory ch pc gamma config proofs batch inputs inverse)
    (identity : Airbender.NativeDelegationSupport.SourceIdentity proofs batch) : Effects proofs batch inputs := by
  have unique := Airbender.NativeMemoryWriteUniquenessProofs.effects embed memory ch pc gamma config accepted identity
  have seeds := Airbender.NativeInitializationSeedBoundaryProofs.boundary embed memory ch pc gamma config accepted
  refine ⟨unique,?_⟩
  intro read write actual
  obtain ⟨source,seed,sink,path,properties,port⟩ := unique.paths.cover read write actual
  have same : read.address = source.address := by
    have selected := (List.mem_filter.mp (properties.ports.mem_iff.mp port)).2
    simpa using selected
  have candidates : ∀ candidate ∈ available proofs batch, candidate.address = read.address → candidate ∈ path := by
    intro candidate member address
    exact on_path Trace.MemoryToken.address seeds.addresses seed properties.first properties.ports
      (fun _ member => Airbender.NativeCompleteMemoryPathProofs.step_address member) member (address.trans same)
  have actualMember := (Airbender.NativeMemoryRootsProofs.step_iff proofs batch _ _).mpr actual
  have old : read ∈ available proofs batch := by
    apply unique.paths.keys.addresses.roots.matching.mem_iff.mpr
    exact List.mem_append_right _ (List.mem_map.mpr ⟨(read,write),actualMember,rfl⟩)
  refine ⟨old,Airbender.NativeCompleteMemoryPathProofs.step_rank unique.paths.keys.addresses.roots.order actualMember,?_,?_⟩
  · intro candidate member address earlier
    exact (path_latest Airbender.NativeCompleteMemoryPaths.rank properties.ordered properties.distinct port
      (candidates candidate member address)).1 earlier
  · intro candidate member address rankEq
    exact (path_latest Airbender.NativeCompleteMemoryPaths.rank properties.ordered properties.distinct port
      (candidates candidate member address)).2 rankEq

theorem counted {Setup R : Type} [Field R] (embed : F →+* R) (memory : MemoryKeyChallenges R)
    (ch : CSRArgumentChallenges R) (pc : PCChallenges R) (gamma : R) (config : WorkerConfiguration Setup)
    {batch : Airbender.NativeMainBatch.Batch R} {workers : WorkerBatch Setup R}
    {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : Airbender.NativeMainBatch.SourceAccepted embed memory ch pc gamma config batch workers inputs inverse)
    (identity : Airbender.NativeDelegationSupport.SourceIdentity batch.proofs workers) :
    Airbender.NativeMainBatch.Effects batch ∧ Effects batch.proofs workers inputs :=
  ⟨Airbender.NativeMainBatchProofs.effects batch accepted.counter,
    effects embed memory ch pc gamma config accepted.component identity⟩
end Airbender.NativeLatestReadsProofs
