import Airbender.Review.Trace.Families.ReducedMachine.WorkerSnapshot
import Airbender.Proofs.ReducedMachine.NativeWorkerTransition

namespace Airbender.NativeWorkerSnapshotProofs
open Airbender.NativeMixedReplay
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

theorem ordered_cut {A : Type} (rank : A → Nat) (items : List A) (time : Nat)
    (ordered : items.Pairwise (fun a b => rank a ≤ rank b)) :
    ∃ prior suffix, items = prior ++ suffix ∧
      (∀ item ∈ prior, rank item < time) ∧ (∀ item ∈ suffix, time ≤ rank item) := by
  induction items with
  | nil => exact ⟨[],[],rfl,by simp,by simp⟩
  | cons first tail ih =>
    have order := List.pairwise_cons.mp ordered
    by_cases earlier : rank first < time
    · obtain ⟨prior,suffix,same,before,after⟩ := ih order.2
      refine ⟨first :: prior,suffix,by simp [same],?_,after⟩
      intro item member
      rcases List.mem_cons.mp member with rfl | member
      · exact earlier
      · exact before item member
    · refine ⟨[],first :: tail,rfl,by simp,?_⟩
      intro item member
      rcases List.mem_cons.mp member with rfl | member
      · omega
      · have := order.1 item member; omega

theorem split_replay {A K : Type} (key : A → K) (prior suffix : List (A × A))
    {initial terminal : List A} (run : Replay key initial (prior ++ suffix) terminal) :
    ∃ snapshot, Replay key initial prior snapshot ∧ Replay key snapshot suffix terminal := by
  induction prior generalizing initial with
  | nil => exact ⟨initial,.done (Airbender.NativeMixedReplayProofs.initial_unique key run) (.refl _),run⟩
  | cons edge tail ih =>
    obtain ⟨read,write⟩ := edge
    cases run with
    | step unique present address next =>
      obtain ⟨snapshot,before,after⟩ := ih next
      exact ⟨snapshot,.step unique present address before,after⟩

/-- A read strictly before a cut cannot originate in any write after the cut. -/
theorem early_read {A K : Type} (key : A → K) (rank : A → Nat) (time : Nat)
    {initial terminal : List A} {edges : List (A × A)}
    (run : Replay key initial edges terminal)
    (after : ∀ edge ∈ edges, time ≤ rank edge.2)
    {read write : A} (member : (read,write) ∈ edges) (earlier : rank read < time) : read ∈ initial := by
  induction run with
  | done _ _ => simp at member
  | @step state rest first output tail terminal unique present address next ih =>
    rcases List.mem_cons.mp member with same | member
    · cases same
      exact present.mem_iff.mpr (by simp)
    · have current := ih (fun edge member => after edge (List.mem_cons_of_mem _ member)) member
      rcases List.mem_cons.mp current with same | current
      · have later := after (first,output) (by simp)
        change time ≤ rank output at later
        rw [same] at earlier
        omega
      · exact present.mem_iff.mpr (List.mem_cons_of_mem _ current)

open Airbender.NativeWorkerSnapshot Airbender.Blake2Worker.Native
open Airbender.ReducedMachine.Native Airbender.Trace Airbender.Verification
open Airbender.ReducedMachine.NativeMemoryBoundary

theorem common_rank (w : Nat → F) (slot : Fin 43) :
    Airbender.NativeCompleteMemoryPaths.rank (write w slot) = Airbender.NativeCompleteMemoryPaths.rank (write w 0) := by
  unfold Airbender.NativeCompleteMemoryPaths.rank
  rw [Airbender.NativeActiveWorkerClockProofs.write_clock,Airbender.NativeActiveWorkerClockProofs.write_clock]

theorem sampled_input (w : Nat → F) : sampledInput (read w) = Airbender.NativeWorkerTransition.readInput w := by
  have values (slot : Fin 43) :
      (Airbender.NativeMemoryTokens.decodeKey (read w slot)).value = keyValue w slot false := by
    exact congrArg MemoryKey.value (Airbender.NativeMemoryTokenProofs.decode_encode (quotientMemoryKey w slot false))
  have state : (fun word : Fin 8 => fun limb : Fin 2 =>
      (Airbender.NativeMemoryTokens.decodeKey (read w ⟨1+word.val,by have := word.isLt; omega⟩)).value[limb]) =
      (Airbender.NativeWorkerTransition.readInput w).state := by
    funext word limb
    rw [values]
    exact Airbender.NativeWorkerTransitionProofs.read_state w word limb
  have extended : (fun word : Fin 16 => fun limb : Fin 2 =>
      (Airbender.NativeMemoryTokens.decodeKey (read w ⟨9+word.val,by have := word.isLt; omega⟩)).value[limb]) =
      (Airbender.NativeWorkerTransition.readInput w).extended := by
    funext word limb
    rw [values]
    exact Airbender.NativeWorkerTransitionProofs.read_extended w word limb
  have message : (fun word : Fin 16 => fun limb : Fin 2 =>
      (Airbender.NativeMemoryTokens.decodeKey (read w ⟨26+word.val,by have := word.isLt; omega⟩)).value[limb]) =
      (Airbender.NativeWorkerTransition.readInput w).message := by
    funext word limb
    rw [values]
    exact Airbender.NativeWorkerTransitionProofs.read_message w word limb
  unfold sampledInput
  rw [state,extended,message,values]
  have control := Airbender.NativeWorkerTransitionProofs.read_control w
  rw [control.1,control.2]

theorem snapshot {Setup R : Type} [Field R]
    {batch : Airbender.NativeMainDecoder.Batch R} {workers : WorkerBatch Setup R} {inputs : PublicBoundary}
    (prior : Airbender.NativeMixedReplay.Effects batch workers inputs)
    {w : Nat → F} (member : w ∈ Airbender.NativeTokenLedger.workerRows workers)
    (active : w constraintsABI.multiplicity = 1) (result : Airbender.NativeWorkerTransition.RowEffects w) :
    ∃ state, AtSnapshot batch.main.proofs workers inputs w state := by
  obtain ⟨ordered,ports,order,run⟩ := prior.replay
  let time := Airbender.NativeCompleteMemoryPaths.rank (write w 0)
  obtain ⟨earlier,later,split,before,after⟩ := ordered_cut
    (fun edge => Airbender.NativeCompleteMemoryPaths.rank edge.2) ordered time order
  rw [split] at run
  obtain ⟨state,first,rest⟩ := split_replay Trace.MemoryToken.address earlier later run
  have actual : ∀ slot, (read w slot,write w slot) ∈ ordered := by
    intro slot
    apply ports.mem_iff.mpr
    exact (Airbender.NativeMemoryRootsProofs.step_iff batch.main.proofs workers _ _).mpr
      (Or.inr ⟨w,member,active,slot,rfl,rfl⟩)
  have pending : ∀ slot, (read w slot,write w slot) ∈ later := by
    intro slot
    have present := actual slot
    rw [split] at present
    rcases List.mem_append.mp present with present | present
    · have bad := before (read w slot,write w slot) present
      change Airbender.NativeCompleteMemoryPaths.rank (write w slot) < time at bad
      rw [common_rank w slot] at bad
      exact False.elim (Nat.lt_irrefl _ bad)
    · exact present
  have latest := prior.words.prior.workers.prior.latest
  have samples : ∀ slot, read w slot ∈ state := by
    intro slot
    have old := latest.reads _ _ (Or.inr ⟨w,member,active,slot,rfl,rfl⟩)
    have earlier : Airbender.NativeCompleteMemoryPaths.rank (read w slot) < time := by
      have before := old.before
      rw [common_rank w slot] at before
      exact before
    exact early_read Trace.MemoryToken.address Airbender.NativeCompleteMemoryPaths.rank time rest after (pending slot) earlier
  have unique := Airbender.NativeMixedReplayProofs.initial_unique Trace.MemoryToken.address rest
  refine ⟨state,⟨earlier,later,by simpa only [← split] using ports,
    by simpa only [← split] using order,first,rest,before,after⟩,unique,samples,?_,
    latest.unique.workerAddresses w member active,?_,?_,result.result⟩
  · intro slot token present same
    exact List.inj_on_of_nodup_map unique present (samples slot) same
  · intro slot
    rw [Airbender.NativeActiveWorkerClockProofs.write_clock,Airbender.NativeActiveWorkerClockProofs.write_clock]
  · intro chosen present
    have same : chosen = read w := by
      funext slot
      exact List.inj_on_of_nodup_map unique (present slot).1 (samples slot) (present slot).2
    rw [same]
    exact sampled_input w
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
    (identity : Airbender.NativeDelegationSupport.SourceIdentity batch.main.proofs workers) : Airbender.NativeWorkerSnapshot.Effects batch workers inputs := by
  have prior := Airbender.NativeWorkerTransitionProofs.counted publicSetup embed memory ch pc gamma decoder config accepted image lookups identity
  exact ⟨prior.1,prior.2,fun w member active => snapshot prior.1 member active (prior.2 w member)⟩
end Airbender.NativeWorkerSnapshotProofs
