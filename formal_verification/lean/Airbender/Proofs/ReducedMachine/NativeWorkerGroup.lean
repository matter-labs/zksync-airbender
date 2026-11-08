import Airbender.Review.Trace.Families.ReducedMachine.WorkerGroup
import Airbender.Proofs.ReducedMachine.NativeWorkerSnapshot
import Mathlib.Data.List.Perm.Subperm

namespace Airbender.NativeWorkerGroupProofs
open Airbender.NativeMixedReplay
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

/-- Distinct addresses and exact common reads derive the whole block. -/
theorem block_replay {A K : Type} [DecidableEq A] (key : A → K)
    (edges : List (A × A)) (state : List A)
    (unique : (state.map key).Nodup)
    (distinct : (edges.map fun edge => key edge.1).Nodup)
    (address : ∀ edge ∈ edges, key edge.1 = key edge.2)
    (reads : ∀ edge ∈ edges, edge.1 ∈ state) :
    ∃ post, Replay key state edges post := by
  induction edges generalizing state with
  | nil => exact ⟨state,.done unique (.refl _)⟩
  | cons edge tail ih =>
    obtain ⟨read,write⟩ := edge
    have present : state.Perm (read :: state.erase read) := List.perm_cons_erase (reads (read,write) (by simp))
    have oldUnique : (key read :: (state.erase read).map key).Nodup := by
      simpa only [List.map_cons] using (present.map key).nodup_iff.mp unique
    have same := address (read,write) (by simp)
    have nextUnique : ((write :: state.erase read).map key).Nodup := by
      simpa only [List.map_cons,← same] using oldUnique
    have nextReads : ∀ edge ∈ tail, edge.1 ∈ write :: state.erase read := by
      intro edge member
      have different : edge.1 ≠ read := by
        intro equal
        have excluded := (List.nodup_cons.mp distinct).1
        apply excluded
        exact List.mem_map.mpr ⟨edge,member,by rw [equal]⟩
      apply List.mem_cons_of_mem
      exact (List.mem_erase_of_ne different).mpr (reads edge (List.mem_cons_of_mem _ member))
    obtain ⟨post,run⟩ := ih (write :: state.erase read) nextUnique (List.nodup_cons.mp distinct).2
      (fun edge member => address edge (List.mem_cons_of_mem _ member)) nextReads
    exact ⟨post,.step unique present same run⟩

/-- The exact token at an untouched address is unchanged. -/
theorem frame {A K : Type} (key : A → K) {state post : List A} {edges : List (A × A)}
    (run : Replay key state edges post) (token : A)
    (outside : ∀ edge ∈ edges, key token ≠ key edge.2) : (token ∈ post ↔ token ∈ state) := by
  induction run with
  | done _ same => exact same.mem_iff.symm
  | @step state rest read write tail terminal unique present address next ih =>
    have noWrite : token ≠ write := fun equal => outside (read,write) (by simp) (congrArg key equal)
    have noRead : token ≠ read := fun equal => outside (read,write) (by simp) ((congrArg key equal).trans address)
    rw [ih (fun edge member => outside edge (List.mem_cons_of_mem _ member))]
    rw [present.mem_iff]
    simp only [List.mem_cons,noWrite,noRead,false_or]

theorem terminal_unique {A K : Type} (key : A → K) {state post : List A} {edges : List (A × A)}
    (run : Replay key state edges post) : (post.map key).Nodup := by
  induction run with
  | done unique same => exact (same.map key).nodup_iff.mp unique
  | step _ _ _ _ ih => exact ih

/-- Every occurrence participates in the residual multiset balance. -/
theorem balance {A K : Type} (key : A → K) {state post : List A} {edges : List (A × A)}
    (run : Replay key state edges post) :
    (state ++ edges.map Prod.snd).Perm (post ++ edges.map Prod.fst) := by
  induction run with
  | done _ same => simpa using same
  | @step state rest read write tail terminal unique present address next ih =>
    have moved := (List.Perm.cons read (List.perm_middle.trans ih)).trans List.perm_middle.symm
    exact (present.append_right (((read,write) :: tail).map Prod.snd)).trans moved

theorem writes_present {A K : Type} (key : A → K) {state post : List A} {edges : List (A × A)}
    (run : Replay key state edges post) (distinct : (edges.map fun edge => key edge.2).Nodup) :
    ∀ edge ∈ edges, edge.2 ∈ post := by
  induction run with
  | done _ _ => simp
  | @step state rest read write tail terminal unique present address next ih =>
    intro edge member
    rcases List.mem_cons.mp member with rfl | member
    · apply (frame key next write ?_).mpr (by simp)
      intro other member same
      exact (List.nodup_cons.mp distinct).1 (List.mem_map.mpr ⟨other,member,same.symm⟩)
    · exact ih (List.nodup_cons.mp distinct).2 edge member

private theorem shuffle {A : Type} (a b c : List A) :
    ((a ++ b) ++ c).Perm (b ++ (a ++ c)) := by
  have swap : (a ++ b).Perm (b ++ a) := List.perm_append_comm
  simpa only [List.append_assoc] using swap.append_right c

/-- Remove an entire executed block from the SAME exact balance. -/
theorem residual_balance {A K : Type} (key : A → K)
    {state post terminal : List A} {edges group rest : List (A × A)}
    (full : Replay key state edges terminal) (block : Replay key state group post)
    (reorder : edges.Perm (group ++ rest)) :
    (post ++ rest.map Prod.snd).Perm (terminal ++ rest.map Prod.fst) := by
  have whole := ((reorder.map Prod.snd).append_left state).symm.trans
    ((balance key full).trans ((reorder.map Prod.fst).append_left terminal))
  have combined : ((post ++ group.map Prod.fst) ++ rest.map Prod.snd).Perm
      ((terminal ++ group.map Prod.fst) ++ rest.map Prod.fst) :=
    ((balance key block).append_right (rest.map Prod.snd)).symm.trans
      (by simpa only [List.map_append,List.append_assoc] using whole)
  exact (List.perm_append_left_iff (group.map Prod.fst)).mp
    ((shuffle post (group.map Prod.fst) (rest.map Prod.snd)).symm.trans
      (combined.trans (shuffle terminal (group.map Prod.fst) (rest.map Prod.fst))))

/-- Every selected edge occurrence is retained, then the residual is replayed. -/
theorem regroup {A K : Type} [DecidableEq A] (key : A → K) (rank : A → Nat) (time : Nat)
    {state terminal : List A} {edges : List (A × A)} (group : List (A × A))
    (run : Replay key state edges terminal)
    (distinct : (group.map fun edge => key edge.1).Nodup)
    (members : ∀ edge ∈ group, edge ∈ edges)
    (reads : ∀ edge ∈ group, edge.1 ∈ state)
    (address : ∀ edge ∈ edges, key edge.1 = key edge.2)
    (progress : ∀ edge ∈ edges, rank edge.1 < rank edge.2)
    (after : ∀ edge ∈ edges, time ≤ rank edge.2) :
    ∃ post rest, edges.Perm (group ++ rest) ∧ Replay key state group post ∧
      Replay key post rest terminal ∧ rest.Pairwise (fun a b => rank a.2 ≤ rank b.2) ∧
      (∀ edge ∈ rest, time ≤ rank edge.2) := by
  have selected : group.Subperm edges := distinct.of_map.subperm members
  obtain ⟨expanded,same,part⟩ := List.subperm_iff.mp selected
  obtain ⟨remaining,moved⟩ := part.exists_perm_append
  have reorder := same.symm.trans moved
  obtain ⟨post,block⟩ := block_replay key group state
    (Airbender.NativeMixedReplayProofs.initial_unique key run) distinct
    (fun edge member => address edge (members edge member)) reads
  have actual : ∀ edge ∈ remaining, edge ∈ edges := by
    intro edge member
    exact reorder.mem_iff.mpr (List.mem_append_right _ member)
  obtain ⟨ordered,permutation,order,replay⟩ := Airbender.NativeMixedReplayProofs.replay_exists key rank remaining post terminal
    (terminal_unique key block) (residual_balance key run block reorder)
    (fun edge member => address edge (actual edge member))
    (fun edge member => progress edge (actual edge member))
  exact ⟨post,ordered,reorder.trans ((List.Perm.refl group).append permutation.symm),block,replay,order,
    fun edge member => after edge (actual edge (permutation.mem_iff.mp member))⟩
open Airbender.NativeWorkerGroup Airbender.NativeWorkerSnapshot Airbender.Blake2Worker.Native
open Airbender.ReducedMachine.Native Airbender.Trace Airbender.Verification
open Airbender.ReducedMachine.NativeMemoryBoundary

theorem port_member (w : Nat → F) (slot : Fin 43) : (read w slot,write w slot) ∈ ports w :=
  List.mem_map.mpr ⟨slot,List.mem_finRange slot,rfl⟩

theorem readonly_value (w : Nat → F) (slot : Fin 43) (h : (memoryAccess slot).writeValue = none) :
    (write w slot).value = (read w slot).value := by
  have equal : keyValue w slot true = keyValue w slot false := by simp [keyValue,h]
  exact congrArg (fun value : Vector F 2 => Nat.pair value[0].val value[1].val) equal

theorem sampled_output (w : Nat → F) : sampledOutput (write w) = Airbender.NativeWorkerTransition.observed w := by
  simp only [sampledOutput,write,Airbender.NativeMemoryTokenProofs.decode_encode]
  rfl

theorem row {Setup R : Type} [Field R]
    {batch : Airbender.NativeMainDecoder.Batch R} {workers : WorkerBatch Setup R} {inputs : PublicBoundary}
    (effects : Airbender.NativeWorkerSnapshot.Effects batch workers inputs)
    {w : Nat → F} (member : w ∈ Airbender.NativeTokenLedger.workerRows workers)
    (active : w constraintsABI.multiplicity = 1) :
    ∃ before after, RowEffects batch.main.proofs workers inputs w before after := by
  obtain ⟨before,snapshot⟩ := effects.snapshots w member active
  obtain ⟨prior,suffix,ledger,_,first,last,priorRanks,suffixRanks⟩ := snapshot.cut
  have actual : ∀ edge ∈ suffix, edge ∈ Airbender.NativeMemoryRoots.steps batch.main.proofs workers := by
    intro edge present
    exact ledger.mem_iff.mp (List.mem_append_right _ present)
  have selected : ∀ edge ∈ ports w, edge ∈ suffix := by
    intro edge present
    obtain ⟨slot,_,rfl⟩ := List.mem_map.mp present
    have full := (Airbender.NativeMemoryRootsProofs.step_iff batch.main.proofs workers _ _).mpr
      (Or.inr ⟨w,member,active,slot,rfl,rfl⟩)
    rcases List.mem_append.mp (ledger.mem_iff.mpr full) with old | pending
    · have bad := priorRanks (read w slot,write w slot) old
      change Airbender.NativeCompleteMemoryPaths.rank (write w slot) < _ at bad
      rw [Airbender.NativeWorkerSnapshotProofs.common_rank w slot] at bad
      exact False.elim (Nat.lt_irrefl _ bad)
    · exact pending
  have writeDistinct : ((ports w).map fun edge => edge.2.address).Nodup := by
    change ((List.finRange 43).map fun slot => (write w slot).address).Nodup
    exact (List.nodup_finRange 43).map snapshot.addresses
  have address : ∀ edge ∈ suffix, edge.1.address = edge.2.address :=
    fun _ present => Airbender.NativeCompleteMemoryPathProofs.step_address (actual _ present)
  have readDistinct : ((ports w).map fun edge => edge.1.address).Nodup := by
    have same : (ports w).map (fun edge => edge.1.address) = (ports w).map (fun edge => edge.2.address) := by
      apply List.map_congr_left
      intro edge present
      exact address edge (selected edge present)
    rw [same]
    exact writeDistinct
  have roots := effects.prior.words.prior.workers.prior.latest.unique.paths.keys.addresses.roots
  obtain ⟨after,rest,reorder,block,remaining,order,ranks⟩ := regroup Trace.MemoryToken.address
    Airbender.NativeCompleteMemoryPaths.rank (Airbender.NativeCompleteMemoryPaths.rank (write w 0)) (ports w) last
    readDistinct selected
    (by intro edge present; obtain ⟨slot,_,rfl⟩ := List.mem_map.mp present; exact snapshot.reads slot)
    address (fun _ present => Airbender.NativeCompleteMemoryPathProofs.step_rank roots.order (actual _ present)) suffixRanks
  have unique := terminal_unique Trace.MemoryToken.address block
  have written : ∀ slot, write w slot ∈ after :=
    fun slot => writes_present Trace.MemoryToken.address block writeDistinct _ (port_member w slot)
  refine ⟨before,after,snapshot,⟨prior,rest,?_,first,block,remaining,priorRanks,order,ranks⟩,unique,written,?_,?_,?_,readonly_value w⟩
  · simpa only [List.append_assoc] using ((List.Perm.refl prior).append reorder).symm.trans ledger
  · intro slot token present same
    exact List.inj_on_of_nodup_map unique present (written slot) same
  · intro token outside
    apply frame Trace.MemoryToken.address block token
    intro edge present
    obtain ⟨slot,_,rfl⟩ := List.mem_map.mp present
    exact outside slot
  · intro old fresh oldPresent newPresent
    have same : fresh = write w := by
      funext slot
      exact List.inj_on_of_nodup_map unique (newPresent slot).1 (written slot) (newPresent slot).2
    rw [same,sampled_output,snapshot.sampled old oldPresent]
    exact snapshot.result
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
    (identity : Airbender.NativeDelegationSupport.SourceIdentity batch.main.proofs workers) : Airbender.NativeWorkerGroup.Effects batch workers inputs := by
  have prior := Airbender.NativeWorkerSnapshotProofs.counted publicSetup embed memory ch pc gamma decoder config accepted image lookups identity
  exact ⟨prior,fun w member active => row prior member active⟩
end Airbender.NativeWorkerGroupProofs
