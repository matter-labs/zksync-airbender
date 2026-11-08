import Airbender.Review.Circuits.ReducedMachine.CompleteMemoryPathsTheorems
import Tests.NativeStageTwoKeys

namespace Airbender.Tests.NativeCompleteMemoryPaths
open Airbender.NativeCompleteMemoryPaths
open Airbender.Blake2Worker.Native Airbender.ReducedMachine.Native Airbender.ReducedMachine.NativeMemoryBoundary
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

/-- Pure finite data, not accepted native/source/physical witnesses. -/
theorem chain_boundary : ([0] : List Nat).Perm [2] = False := by decide +kernel

theorem chain_matching : ([0,1,2] : List Nat).Perm [2,0,1] := by decide +kernel

theorem duplicate_seed_not_unique : ¬ ([0,0] : List Nat).Nodup := by decide +kernel

theorem duplicate_seed_fork_matching : ([0,0,1,2] : List Nat).Perm [1,2,0,0] := by decide +kernel

theorem single_seed_fork_rejected : ¬ ([0,1,2] : List Nat).Perm [1,2,0,0] := by decide +kernel

private theorem chain_paths : ∃ sink ∈ [2], (0 : Nat) = 0 ∧ ∃ path : List Nat,
    path.head? = some 0 ∧ path.getLast? = some sink ∧ (path.map id).Pairwise (· < ·) ∧
      (path.map id).Nodup ∧ (path.zip path.tail).Perm [(0,1),(1,2)] := by
  have preserved : ∀ edge ∈ ([(0,1),(1,2)] : List (Nat × Nat)), (0 : Nat) = 0 := by
    intro edge member
    rfl
  have increases : ∀ edge ∈ ([(0,1),(1,2)] : List (Nat × Nat)), edge.1 < edge.2 := by
    intro edge member
    simp at member
    rcases member with rfl | rfl <;> decide +kernel
  have paths := Airbender.NativeCompleteMemoryPathProofs.finite_paths (fun _ : Nat => (0 : Nat)) id
    (initial := [0]) (terminal := [2]) (steps := [(0,1),(1,2)])
    (by decide +kernel) preserved (by decide +kernel) increases 0 (by decide +kernel)
  simpa using paths

theorem complete_chain : ∃ path : List Nat, (path.zip path.tail).Perm [(0,1),(1,2)] := by
  obtain ⟨sink,_,_,path,_,_,_,_,ports⟩ := chain_paths
  exact ⟨path,ports⟩

theorem complete_chain_counts : ∃ path : List Nat, (path.zip path.tail).length = 2 := by
  obtain ⟨path,ports⟩ := complete_chain
  exact ⟨path,by simpa using ports.length_eq⟩

theorem empty_address_path : ∃ path : List Nat, path.head? = some 0 ∧ path.getLast? = some 0 ∧
    (path.map id).Nodup ∧ path.zip path.tail = [] := ⟨[0],rfl,rfl,by decide +kernel,rfl⟩

theorem separate_addresses_same_rank :
    ∃ sink ∈ [(0,1),(1,1)], sink.1 = (0 : Nat) ∧ ∃ path : List (Nat × Nat),
      path.head? = some (0,0) ∧ path.getLast? = some sink ∧ (path.map Prod.snd).Pairwise (· < ·) ∧
        (path.map Prod.snd).Nodup ∧ (path.zip path.tail).Perm [((0,0),(0,1))] := by
  have preserved : ∀ edge ∈ ([((0,0),(0,1)),((1,0),(1,1))] : List ((Nat × Nat) × (Nat × Nat))),
      edge.1.1 = edge.2.1 := by
    intro edge member
    simp at member
    rcases member with rfl | rfl <;> rfl
  have increases : ∀ edge ∈ ([((0,0),(0,1)),((1,0),(1,1))] : List ((Nat × Nat) × (Nat × Nat))),
      edge.1.2 < edge.2.2 := by
    intro edge member
    simp at member
    rcases member with rfl | rfl <;> decide +kernel
  have paths := Airbender.NativeCompleteMemoryPathProofs.finite_paths Prod.fst Prod.snd
    (initial := [(0,0),(1,0)]) (terminal := [(0,1),(1,1)]) (steps := [((0,0),(0,1)),((1,0),(1,1))])
    (by decide +kernel) preserved (by decide +kernel) increases (0,0) (by decide +kernel)
  simpa using paths

theorem terminal_addresses_unique {Setup R : Type} [Field R]
    {proofs : List (Airbender.NativeInitializationBatch.Proof R)} {batch : WorkerBatch Setup R} {inputs : PublicBoundary}
    (result : Effects proofs batch inputs) :
    ((Airbender.NativeInitializationSeedBoundary.terminalTokens proofs inputs).map Trace.MemoryToken.address).Nodup :=
  result.terminal

theorem actual_port_covered {Setup R : Type} [Field R]
    {proofs : List (Airbender.NativeInitializationBatch.Proof R)} {batch : WorkerBatch Setup R} {inputs : PublicBoundary}
    (result : Effects proofs batch inputs) {read write : Token}
    (edge : Airbender.NativeMixedMemoryOrder.Step proofs batch read write) :
    ∃ source ∈ Airbender.NativeInitializationSeedBoundary.initialTokens proofs, ∃ sink path,
      AddressPath proofs batch inputs source sink path ∧ (read,write) ∈ path.zip path.tail := result.cover read write edge

theorem inactive_source_read_stays {Setup R : Type} [Field R]
    (proofs : List (Airbender.NativeInitializationBatch.Proof R)) {batch : WorkerBatch Setup R}
    {w : Nat → F} (member : w ∈ Airbender.NativeTokenLedger.workerRows batch)
    (zero : w constraintsABI.multiplicity = 0) (slot : Fin 43) :
    w constraintsABI.multiplicity = 0 ∧ Airbender.NativeWorkerClockProgress.readToken w slot ∈
      Airbender.NativeInitializationSeedBoundary.accessTokens proofs batch false :=
  ⟨zero,Airbender.NativeWorkerClockProgressProofs.read_member proofs member slot⟩

theorem all32_register_seeds : Airbender.NativeInitializationSeedBoundary.initialRegisters.length = 32 := by
  simp [Airbender.NativeInitializationSeedBoundary.initialRegisters]

theorem zero_factor_retained : memoryKeyArgument (RingHom.id F) ⟨0,0,0,0,0,0,0⟩
    ⟨⟨0,4,0⟩,#v[0,0],#v[0,0]⟩ = 0 := Airbender.Tests.NativeStageTwoKeys.zero_factor_stays

theorem complete_conditional {Setup R : Type} [Field R]
    (embed : F →+* R) (memory : MemoryKeyChallenges R) (ch : CSRArgumentChallenges R)
    (pc : PCChallenges R) (gamma : R) (config : WorkerConfiguration Setup)
    {proofs : List (Airbender.NativeInitializationBatch.Proof R)} {workers : WorkerBatch Setup R}
    {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : Airbender.NativeInitializationBatch.Accepted embed memory ch pc gamma config proofs workers inputs inverse)
    (identity : Airbender.NativeDelegationSupport.SourceIdentity proofs workers) : Effects proofs workers inputs :=
  native_complete_memory_paths embed memory ch pc gamma config accepted identity

theorem complete_conditional_counted {Setup R : Type} [Field R]
    (embed : F →+* R) (memory : MemoryKeyChallenges R) (ch : CSRArgumentChallenges R)
    (pc : PCChallenges R) (gamma : R) (config : WorkerConfiguration Setup)
    {batch : Airbender.NativeMainBatch.Batch R} {workers : WorkerBatch Setup R}
    {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : Airbender.NativeMainBatch.SourceAccepted embed memory ch pc gamma config batch workers inputs inverse)
    (identity : Airbender.NativeDelegationSupport.SourceIdentity batch.proofs workers) :
    Airbender.NativeMainBatch.Effects batch ∧ Effects batch.proofs workers inputs :=
  native_counted_complete_memory_paths embed memory ch pc gamma config accepted identity

end Airbender.Tests.NativeCompleteMemoryPaths
