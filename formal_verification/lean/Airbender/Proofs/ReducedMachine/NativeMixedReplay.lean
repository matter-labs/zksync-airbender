import Airbender.Review.Trace.Families.ReducedMachine.MixedReplay
import Airbender.Proofs.ReducedMachine.NativeMixedWordBounds

namespace Airbender.NativeMixedReplayProofs
open Airbender.NativeMixedReplay
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

/-- Full multiset balance and strict per-edge progress imply exact online
    token replay in any nondecreasing write-rank order. Equal ranks at different
    addresses are allowed. The rank is only a proof order. -/
theorem replay_sorted {A K : Type} [DecidableEq A] (key : A → K) (rank : A → Nat)
    (edges : List (A × A)) (state terminal : List A)
    (unique : (state.map key).Nodup)
    (matched : (state ++ edges.map Prod.snd).Perm (terminal ++ edges.map Prod.fst))
    (address : ∀ edge ∈ edges, key edge.1 = key edge.2)
    (progress : ∀ edge ∈ edges, rank edge.1 < rank edge.2)
    (ordered : edges.Pairwise (fun a b => rank a.2 ≤ rank b.2)) :
    Replay key state edges terminal := by
  induction edges generalizing state with
  | nil =>
    exact .done unique (by simpa using matched)
  | cons edge tail ih =>
    obtain ⟨read,write⟩ := edge
    have increasing : rank read < rank write := progress (read,write) (by simp)
    have same := address (read,write) (by simp)
    have order := List.pairwise_cons.mp ordered
    have source : read ∈ state := by
      have member : read ∈ state ++ ((read,write) :: tail).map Prod.snd :=
        matched.mem_iff.mpr (List.mem_append_right _ (by simp))
      rcases List.mem_append.mp member with member | member
      · exact member
      · obtain ⟨other,present,equal⟩ := List.mem_map.mp member
        rcases List.mem_cons.mp present with rfl | present
        · dsimp only at equal
          subst write
          omega
        · have later : rank write ≤ rank other.2 := order.1 other present
          rw [equal] at later
          omega
    let rest := state.erase read
    have splitState : state.Perm (read :: rest) := List.perm_cons_erase source
    have distinct : (key read :: rest.map key).Nodup := by
      simpa only [List.map_cons] using (splitState.map key).nodup_iff.mp unique
    have nextUnique : ((write :: rest).map key).Nodup := by
      simpa only [List.map_cons,← same] using distinct
    have nextMatched : ((write :: rest) ++ tail.map Prod.snd).Perm
        (terminal ++ tail.map Prod.fst) := by
      have moved := (splitState.append_right (((read,write) :: tail).map Prod.snd)).symm.trans matched
      change (read :: (rest ++ write :: tail.map Prod.snd)).Perm
        (terminal ++ read :: tail.map Prod.fst) at moved
      exact List.perm_middle.symm.trans (moved.trans List.perm_middle).cons_inv
    refine .step unique splitState same (ih (write :: rest) nextUnique nextMatched ?_ ?_ order.2)
    · intro other member
      exact address other (List.mem_cons_of_mem _ member)
    · intro other member
      exact progress other (List.mem_cons_of_mem _ member)

/-- Sort positions without discarding copies or requiring globally unique ranks. -/
theorem replay_exists {A K : Type} [DecidableEq A] (key : A → K) (rank : A → Nat)
    (edges : List (A × A)) (initial terminal : List A)
    (unique : (initial.map key).Nodup)
    (matched : (initial ++ edges.map Prod.snd).Perm (terminal ++ edges.map Prod.fst))
    (address : ∀ edge ∈ edges, key edge.1 = key edge.2)
    (progress : ∀ edge ∈ edges, rank edge.1 < rank edge.2) :
    ∃ ordered, ordered.Perm edges ∧
      ordered.Pairwise (fun a b => rank a.2 ≤ rank b.2) ∧ Replay key initial ordered terminal := by
  let ordered := edges.mergeSort (fun a b => decide (rank a.2 ≤ rank b.2))
  have permutation : ordered.Perm edges := List.mergeSort_perm _ _
  have order : ordered.Pairwise (fun a b => rank a.2 ≤ rank b.2) := by
    have sorted := List.pairwise_mergeSort
      (le := fun a b : A × A => decide (rank a.2 ≤ rank b.2))
      (by intro a b c ab bc; simp only [decide_eq_true_eq] at *; omega)
      (by intro a b; simp only [Bool.or_eq_true,decide_eq_true_eq]; omega) edges
    simpa only [decide_eq_true_eq] using sorted
  refine ⟨ordered,permutation,order,replay_sorted key rank ordered initial terminal unique ?_ ?_ ?_ order⟩
  · exact ((permutation.map Prod.snd).append_left initial).trans
      (matched.trans ((permutation.map Prod.fst).append_left terminal).symm)
  · intro edge member
    exact address edge (permutation.mem_iff.mp member)
  · intro edge member
    exact progress edge (permutation.mem_iff.mp member)
open Airbender.NativeMixedReplay
open Airbender.Blake2Worker.Native Airbender.ReducedMachine.NativeMemoryBoundary
open Airbender.ReducedMachine.Native Airbender.Trace Airbender.Verification
private abbrev F := ZMod mersenne31Modulus

theorem initial_unique {A K : Type} (key : A → K) {state terminal : List A}
    {edges : List (A × A)} (run : Replay key state edges terminal) : (state.map key).Nodup := by
  cases run with
  | done unique _ => exact unique
  | step unique _ _ _ => exact unique

theorem head_read {A K : Type} (key : A → K) {state terminal : List A}
    {read write : A} {edges : List (A × A)}
    (run : Replay key state ((read,write) :: edges) terminal)
    {candidate : A} (member : candidate ∈ state) (same : key candidate = key read) : candidate = read := by
  cases run with
  | step unique present _ _ =>
    exact List.inj_on_of_nodup_map unique member (present.mem_iff.mpr (by simp)) same

theorem from_roots {Setup R : Type} [Field R]
    {proofs : List (Airbender.NativeInitializationBatch.Proof R)} {workers : WorkerBatch Setup R}
    {inputs : PublicBoundary}
    (roots : Airbender.NativeMemoryRoots.Effects proofs workers inputs)
    (seeds : Airbender.NativeInitializationSeedBoundary.Effects proofs) : Execution proofs workers inputs := by
  exact replay_exists Trace.MemoryToken.address Airbender.NativeCompleteMemoryPaths.rank
    (Airbender.NativeMemoryRoots.steps proofs workers)
    (Airbender.NativeInitializationSeedBoundary.initialTokens proofs)
    (Airbender.NativeInitializationSeedBoundary.terminalTokens proofs inputs)
    seeds.addresses roots.matching
    (fun _ member => Airbender.NativeCompleteMemoryPathProofs.step_address member)
    (fun _ member => Airbender.NativeCompleteMemoryPathProofs.step_rank roots.order member)

theorem effects {Setup R : Type} [Field R] (embed : F →+* R) (memory : MemoryKeyChallenges R)
    (ch : CSRArgumentChallenges R) (pc : PCChallenges R) (gamma : R) (config : WorkerConfiguration Setup)
    {proofs : List (Airbender.NativeInitializationBatch.Proof R)} {workers : WorkerBatch Setup R}
    {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : Airbender.NativeInitializationBatch.Accepted embed memory ch pc gamma config proofs workers inputs inverse)
    (identity : Airbender.NativeDelegationSupport.SourceIdentity proofs workers) : Execution proofs workers inputs :=
  from_roots (Airbender.NativeMemoryRootsProofs.effects embed memory ch pc gamma config accepted identity)
    (Airbender.NativeInitializationSeedBoundaryProofs.boundary embed memory ch pc gamma config accepted)

theorem counted {Setup R : Type} [Field R]
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
    (identity : Airbender.NativeDelegationSupport.SourceIdentity batch.main.proofs workers) : Effects batch workers inputs := by
  have words := Airbender.NativeMixedWordBoundsProofs.counted publicSetup embed memory ch pc gamma decoder config accepted image lookups identity
  exact ⟨words,from_roots words.prior.workers.prior.latest.unique.paths.keys.addresses.roots
    (Airbender.NativeInitializationSeedBoundaryProofs.boundary embed memory ch pc gamma config accepted.counted.component)⟩
end Airbender.NativeMixedReplayProofs
