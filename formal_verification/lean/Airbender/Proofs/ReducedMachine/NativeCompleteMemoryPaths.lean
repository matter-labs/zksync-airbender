import Airbender.Review.Circuits.ReducedMachine.CompleteMemoryPaths
import Airbender.Proofs.ReducedMachine.NativeStageTwoKeys
import Airbender.Proofs.Trace.MemoryPaths

namespace Airbender.NativeCompleteMemoryPathProofs
open Airbender.NativeCompleteMemoryPaths
open Airbender.Blake2Worker.Native Airbender.ReducedMachine.Native Airbender.ReducedMachine.NativeMemoryBoundary
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

/-- Reuse the unchanged generic finite-support Clean path theorem BEFORE
    native/domain instantiation. The support construction retains all counts. -/
theorem finite_paths {S K : Type} [DecidableEq S] [DecidableEq K]
    (key : S → K) (order : S → Nat) {initial terminal : List S} {steps : List (S × S)}
    (matched : (initial ++ steps.map Prod.snd).Perm (terminal ++ steps.map Prod.fst))
    (preserved : ∀ edge ∈ steps, key edge.1 = key edge.2)
    (unique : (initial.map key).Nodup)
    (increases : ∀ edge ∈ steps, order edge.1 < order edge.2) :
    ∀ source ∈ initial, ∃ sink ∈ terminal, key sink = key source ∧
      ∃ path : List S, path.head? = some source ∧ path.getLast? = some sink ∧
        (path.map order).Pairwise (· < ·) ∧ (path.map order).Nodup ∧
        (path.zip path.tail).Perm (steps.filter fun edge => key edge.1 = key source) := by
  have paths := Airbender.Trace.Proofs.keyed_paths_finite key order matched preserved unique increases
  intro source member
  obtain ⟨sink,present,same,path,first,last,distinct,ports⟩ := paths source member
  have ascending : ∀ edge ∈ path.zip path.tail, order edge.1 < order edge.2 := by
    intro edge actual
    exact increases edge (List.mem_of_mem_filter (ports.mem_iff.mp actual))
  exact ⟨sink,present,same,path,first,last,Airbender.Trace.Proofs.rank_ordered order path ascending,distinct,ports⟩

theorem step_rank {Setup R : Type} [Field R]
    {proofs : List (Airbender.NativeInitializationBatch.Proof R)} {batch : WorkerBatch Setup R}
    (order : Airbender.NativeMixedMemoryOrder.Effects proofs batch) {edge : Token × Token}
    (member : edge ∈ Airbender.NativeMemoryRoots.steps proofs batch) : rank edge.1 < rank edge.2 := by
  have actual := (Airbender.NativeMemoryRootsProofs.step_iff proofs batch _ _).mp member
  have increase := order.steps _ _ actual
  have nonnegative := order.workers.reads _ (Airbender.NativeMixedMemoryOrderProofs.step_read_member actual)
  unfold rank
  omega

theorem step_address {Setup R : Type} [Field R]
    {proofs : List (Airbender.NativeInitializationBatch.Proof R)} {batch : WorkerBatch Setup R}
    {edge : Token × Token} (member : edge ∈ Airbender.NativeMemoryRoots.steps proofs batch) :
    edge.1.address = edge.2.address :=
  Airbender.NativeAddressSupportProofs.step_address
    ((Airbender.NativeMemoryRootsProofs.step_iff proofs batch _ _).mp member)

theorem effects {Setup R : Type} [Field R] (embed : F →+* R) (memory : MemoryKeyChallenges R)
    (ch : CSRArgumentChallenges R) (pc : PCChallenges R) (gamma : R) (config : WorkerConfiguration Setup)
    {proofs : List (Airbender.NativeInitializationBatch.Proof R)} {batch : WorkerBatch Setup R}
    {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : Airbender.NativeInitializationBatch.Accepted embed memory ch pc gamma config proofs batch inputs inverse)
    (identity : Airbender.NativeDelegationSupport.SourceIdentity proofs batch) : Effects proofs batch inputs := by
  have keys := Airbender.NativeStageTwoKeyProofs.effects embed memory ch pc gamma config accepted identity
  have seeds := Airbender.NativeInitializationSeedBoundaryProofs.boundary embed memory ch pc gamma config accepted
  have matched := keys.addresses.roots.matching
  have boundary := Airbender.Trace.Proofs.boundary_keys Trace.MemoryToken.address matched (fun _ member => step_address member)
  have paths := finite_paths Trace.MemoryToken.address rank matched (fun _ member => step_address member)
    seeds.addresses (fun _ member => step_rank keys.addresses.roots.order member)
  have allPaths : ∀ source ∈ Airbender.NativeInitializationSeedBoundary.initialTokens proofs,
      ∃ sink path, AddressPath proofs batch inputs source sink path := by
    intro source member
    obtain ⟨sink,present,same,path,first,last,ordered,distinct,ports⟩ := paths source member
    exact ⟨sink,path,present,same,first,last,ordered,distinct,ports⟩
  refine ⟨keys,boundary,boundary.nodup_iff.mp seeds.addresses,allPaths,?_⟩
  intro read write actual
  obtain ⟨source,member,path⟩ := keys.addresses.roots.reads read write actual
  have same : source.address = read.address := Airbender.NativeAddressSupportProofs.path_invariant _
    Trace.MemoryToken.address (fun _ _ edge => Airbender.NativeAddressSupportProofs.step_address edge) path
  obtain ⟨sink,complete,properties⟩ := allPaths source member
  have port : (read,write) ∈ Airbender.NativeMemoryRoots.steps proofs batch :=
    (Airbender.NativeMemoryRootsProofs.step_iff proofs batch _ _).mpr actual
  have selected : (read,write) ∈ (Airbender.NativeMemoryRoots.steps proofs batch).filter
      (fun edge => edge.1.address = source.address) :=
    List.mem_filter.mpr ⟨port,by simpa using same.symm⟩
  exact ⟨source,member,sink,complete,properties,properties.ports.mem_iff.mpr selected⟩

theorem counted {Setup R : Type} [Field R] (embed : F →+* R) (memory : MemoryKeyChallenges R)
    (ch : CSRArgumentChallenges R) (pc : PCChallenges R) (gamma : R) (config : WorkerConfiguration Setup)
    {batch : Airbender.NativeMainBatch.Batch R} {workers : WorkerBatch Setup R}
    {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : Airbender.NativeMainBatch.SourceAccepted embed memory ch pc gamma config batch workers inputs inverse)
    (identity : Airbender.NativeDelegationSupport.SourceIdentity batch.proofs workers) :
    Airbender.NativeMainBatch.Effects batch ∧ Effects batch.proofs workers inputs :=
  ⟨Airbender.NativeMainBatchProofs.effects batch accepted.counter,
    effects embed memory ch pc gamma config accepted.component identity⟩
end Airbender.NativeCompleteMemoryPathProofs
