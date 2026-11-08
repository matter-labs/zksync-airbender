import Airbender.Review.Circuits.ReducedMachine.MemoryWriteUniqueness
import Airbender.Proofs.ReducedMachine.NativeCompleteMemoryPaths

namespace Airbender.NativeMemoryWriteUniquenessProofs
open Airbender.NativeMemoryWriteUniqueness
open Airbender.Blake2Worker.Native Airbender.ReducedMachine.Native Airbender.ReducedMachine.NativeMemoryBoundary
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

/-- Generic occurrence-sensitive grouping, BEFORE any native data. -/
theorem grouped_nodup {A K V : Type} [DecidableEq K] (key : A → K) (value : A → V)
    (items : List A)
    (each : ∀ item ∈ items, ((items.filter fun other => key other = key item).map value).Nodup) :
    (items.map fun item => (key item,value item)).Nodup := by
  induction items with
  | nil => simp
  | cons first rest ih =>
    have selected := each first (by simp)
    simp only [List.filter_cons,decide_true,ite_true,List.map_cons] at selected
    apply List.nodup_cons.mpr
    constructor
    · intro member
      obtain ⟨item,present,same⟩ := List.mem_map.mp member
      have address := congrArg Prod.fst same
      have output := congrArg Prod.snd same
      exact (List.nodup_cons.mp selected).1 (List.mem_map.mpr
        ⟨item,List.mem_filter.mpr ⟨present,by simpa using address⟩,output⟩)
    · apply ih
      intro item member
      have selected := each item (List.mem_cons_of_mem first member)
      simp only [List.filter_cons] at selected
      split at selected
      · exact (List.nodup_cons.mp selected).2
      · exact selected

private theorem zip_outputs {S V : Type} (value : S → V) (path : List S) :
    ((path.zip path.tail).map fun edge => value edge.2) = path.tail.map value := by
  induction path with
  | nil => rfl
  | cons first rest ih =>
    cases rest with
    | nil => rfl
    | cons second tail => simpa using congrArg (List.cons (value second)) ih

/-- Exact counted paths imply unique (address,write-rank) occurrences. No
    assumption about distinct global ranks or distinct edge positions is added. -/
theorem unique_writes {S K : Type} [DecidableEq S] [DecidableEq K]
    (key : S → K) (rank : S → Nat) {initial terminal : List S} {steps : List (S × S)}
    (matched : (initial ++ steps.map Prod.snd).Perm (terminal ++ steps.map Prod.fst))
    (preserved : ∀ edge ∈ steps, key edge.1 = key edge.2)
    (unique : (initial.map key).Nodup)
    (increases : ∀ edge ∈ steps, rank edge.1 < rank edge.2) :
    (steps.map fun edge => (key edge.2,rank edge.2)).Nodup := by
  have paths := Airbender.NativeCompleteMemoryPathProofs.finite_paths key rank matched preserved unique increases
  have origins := Airbender.Trace.Proofs.keyed_origins key rank matched preserved increases
  have distinct : (steps.map fun edge => (key edge.1,rank edge.2)).Nodup := by
    apply grouped_nodup (fun edge => key edge.1) (fun edge => rank edge.2) steps
    intro edge member
    obtain ⟨source,present,same⟩ := List.mem_map.mp (origins edge member)
    obtain ⟨sink,_,_,path,_,_,_,ranks,ports⟩ := paths source present
    have projection := ports.map (fun edge => rank edge.2)
    rw [zip_outputs] at projection
    have tail : (path.tail.map rank).Nodup := by simpa only [List.map_tail] using ranks.tail
    have result := projection.nodup_iff.mp tail
    simpa only [same] using result
  have same : (steps.map fun edge => (key edge.2,rank edge.2)) =
      (steps.map fun edge => (key edge.1,rank edge.2)) := by
    apply List.map_congr_left
    intro edge member
    rw [preserved edge member]
  rw [same]
  exact distinct

/-- One observed segment remains a sublist, including every positional copy. -/
theorem flatMap_segment {A B : Type} (f : A → List B) {items : List A} {item : A}
    (member : item ∈ items) : (f item).Sublist (items.flatMap f) := by
  induction items with
  | nil => simp at member
  | cons first rest ih =>
    rcases List.mem_cons.mp member with rfl | member
    · exact List.sublist_append_left _ _
    · exact (ih member).trans (List.sublist_append_right _ _)

theorem worker_segment {Setup R : Type} [Field R]
    (proofs : List (Airbender.NativeInitializationBatch.Proof R)) {batch : WorkerBatch Setup R}
    {w : Nat → F} (member : w ∈ Airbender.NativeTokenLedger.workerRows batch)
    (active : w constraintsABI.multiplicity = 1) :
    (Airbender.NativeMemoryRoots.workerSteps w).Sublist (Airbender.NativeMemoryRoots.steps proofs batch) := by
  have part := flatMap_segment (fun row => if row constraintsABI.multiplicity = 1 then
    Airbender.NativeMemoryRoots.workerSteps row else []) member
  rw [if_pos active] at part
  exact part.trans (List.sublist_append_right _ _)

theorem worker_addresses {Setup R : Type} [Field R]
    {proofs : List (Airbender.NativeInitializationBatch.Proof R)} {batch : WorkerBatch Setup R}
    (writes : ((Airbender.NativeMemoryRoots.steps proofs batch).map fun edge => writeKey edge.2).Nodup)
    {w : Nat → F} (member : w ∈ Airbender.NativeTokenLedger.workerRows batch)
    (active : w constraintsABI.multiplicity = 1) : Function.Injective
      (fun slot : Fin 43 => (Airbender.NativeMemoryTokens.encodeKey (quotientMemoryKey w slot true)).address) := by
  have slots := writes.sublist ((worker_segment proofs member active).map (fun edge => writeKey edge.2))
  change ((List.finRange 43).map fun slot => writeKey
    (Airbender.NativeMemoryTokens.encodeKey (quotientMemoryKey w slot true))).Nodup at slots
  intro left right same
  apply List.inj_on_of_nodup_map slots (List.mem_finRange left) (List.mem_finRange right)
  apply Prod.ext same
  unfold writeKey Airbender.NativeCompleteMemoryPaths.rank
  rw [Airbender.NativeActiveWorkerClockProofs.write_clock,Airbender.NativeActiveWorkerClockProofs.write_clock]

theorem effects {Setup R : Type} [Field R] (embed : F →+* R) (memory : MemoryKeyChallenges R)
    (ch : CSRArgumentChallenges R) (pc : PCChallenges R) (gamma : R) (config : WorkerConfiguration Setup)
    {proofs : List (Airbender.NativeInitializationBatch.Proof R)} {batch : WorkerBatch Setup R}
    {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : Airbender.NativeInitializationBatch.Accepted embed memory ch pc gamma config proofs batch inputs inverse)
    (identity : Airbender.NativeDelegationSupport.SourceIdentity proofs batch) : Effects proofs batch inputs := by
  have paths := Airbender.NativeCompleteMemoryPathProofs.effects embed memory ch pc gamma config accepted identity
  have seeds := Airbender.NativeInitializationSeedBoundaryProofs.boundary embed memory ch pc gamma config accepted
  have writes := unique_writes Trace.MemoryToken.address Airbender.NativeCompleteMemoryPaths.rank
    paths.keys.addresses.roots.matching (fun _ member => Airbender.NativeCompleteMemoryPathProofs.step_address member)
    seeds.addresses (fun _ member => Airbender.NativeCompleteMemoryPathProofs.step_rank paths.keys.addresses.roots.order member)
  exact ⟨paths,writes,fun _ member active => worker_addresses writes member active⟩

theorem counted {Setup R : Type} [Field R] (embed : F →+* R) (memory : MemoryKeyChallenges R)
    (ch : CSRArgumentChallenges R) (pc : PCChallenges R) (gamma : R) (config : WorkerConfiguration Setup)
    {batch : Airbender.NativeMainBatch.Batch R} {workers : WorkerBatch Setup R}
    {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : Airbender.NativeMainBatch.SourceAccepted embed memory ch pc gamma config batch workers inputs inverse)
    (identity : Airbender.NativeDelegationSupport.SourceIdentity batch.proofs workers) :
    Airbender.NativeMainBatch.Effects batch ∧ Effects batch.proofs workers inputs :=
  ⟨Airbender.NativeMainBatchProofs.effects batch accepted.counter,
    effects embed memory ch pc gamma config accepted.component identity⟩
end Airbender.NativeMemoryWriteUniquenessProofs
