import Airbender.Review.Trace.Families.ReducedMachine.ControlSource
import Airbender.Proofs.ReducedMachine.NativeControlFold
import Mathlib.Algebra.BigOperators.Fin

namespace Airbender.NativeControlSourceProofs
open Airbender.NativeWorkerSnapshot Airbender.NativeControlHistory Airbender.NativeControlLogic
open Airbender.NativeControlFold Airbender.NativeControlLastReset Airbender.NativeControlSource
open Airbender.ReducedMachine Airbender.ReducedMachine.Native Airbender.Trace
open Airbender.Blake2Worker.Native Airbender.ReducedMachine.NativeMemoryBoundary
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

/-- Generic edge occurrence selection before native data. -/
theorem edge_position {A : Type} {path : List A} {edge : A × A} (member : edge ∈ path.zip path.tail) :
    ∃ index : Fin (path.length-1), pathEdge path index = edge := by
  induction path with
  | nil => simp at member
  | cons first rest ih =>
    cases rest with
    | nil => simp at member
    | cons second tail =>
      rcases List.mem_cons.mp member with same | later
      · exact ⟨⟨0,by simp⟩,same.symm⟩
      · obtain ⟨index,equal⟩ := ih later
        refine ⟨⟨index.val + 1,by have := index.isLt; simp only [List.length_cons] at *; omega⟩,?_⟩
        simpa only [pathEdge,List.getElem_cons_succ] using equal

theorem edge_injective {A K : Type} {path : List A} (rank : A → K) (unique : (path.map rank).Nodup) :
    Function.Injective (pathEdge path) := by
  have values := List.Nodup.of_map rank unique
  intro i j same
  have first : path[i.val] = path[j.val] := congrArg Prod.fst same
  have equal : (⟨i.val,by have := i.isLt; omega⟩ : Fin path.length) = ⟨j.val,by have := j.isLt; omega⟩ :=
    List.nodup_iff_injective_getElem.mp values first
  exact Fin.ext (congrArg (fun k : Fin path.length => k.val) equal)

theorem segment_injective {A K : Type} {path : List A} (rank : A → K) (unique : (path.map rank).Nodup)
    (target : Fin path.length) (start : Fin (target.val + 1)) :
    Function.Injective (fun index : Fin (target.val-start.val) =>
      edgeAt path target ⟨start.val + index.val,by have := index.isLt; omega⟩) := by
  intro i j same
  have equal : (⟨start.val + i.val,by have := i.isLt; have := target.isLt; omega⟩ : Fin (path.length-1)) =
      ⟨start.val + j.val,by have := j.isLt; have := target.isLt; omega⟩ := edge_injective rank unique same
  apply Fin.ext
  have coords := congrArg Fin.val equal
  change start.val + i.val = start.val + j.val at coords
  omega

/-- Generic cardinality of a relation with unique partners in BOTH directions. -/
theorem matching_card {A B : Type} [Fintype A] [Fintype B] (rel : A → B → Prop)
    (left : ∀ a, ∃! b, rel a b) (right : ∀ b, ∃! a, rel a b) : Fintype.card A = Fintype.card B := by
  classical
  let partner (a : A) : B := Classical.choose (left a)
  have holds (a : A) : rel a (partner a) := (Classical.choose_spec (left a)).1
  apply Fintype.card_of_bijective (f := partner)
  constructor
  · intro a b same
    obtain ⟨chosen,_,only⟩ := right (partner a)
    exact (only a (holds a)).trans (only b (by rw [same]; exact holds b)).symm
  · intro b
    obtain ⟨a,matched,_⟩ := right b
    exact ⟨a,(Classical.choose_spec (left a)).2 b matched |>.symm⟩

theorem flags_card (n : Nat) (flags : Fin n → Bool) :
    countFlags flags = Fintype.card {index // flags index = true} := by
  classical
  have sums : countFlags flags = ∑ index : Fin n, if flags index then 1 else 0 := by
    induction n with
    | zero => simp [countFlags]
    | succ n ih => simpa only [countFlags,Fin.sum_univ_castSucc] using congrArg (fun x => x + if flags (Fin.last n) then 1 else 0) (ih (fun i => flags i.castSucc))
  rw [Fintype.card_subtype,Finset.card_eq_sum_ones,Finset.sum_filter]
  exact sums

theorem source_unique {Setup R : Type} [Field R] {workers : WorkerBatch Setup R}
    (clocks : ((Airbender.NativeDelegationKeyAccounting.activeRows workers).map Airbender.NativeActiveWorkerClocks.workerClock).Nodup)
    {edge : Token × Token} (selected : WorkerEdge workers edge) : ∃! source, SourceAt workers edge source := by
  classical
  obtain ⟨w,wm,active,same⟩ := selected
  have member : Airbender.NativeActiveWorkerClocks.workerClock w ∈
      (Airbender.NativeDelegationKeyAccounting.activeRows workers).map Airbender.NativeActiveWorkerClocks.workerClock :=
    List.mem_map.mpr ⟨w,List.mem_filter.mpr ⟨wm,by simpa using active⟩,rfl⟩
  have one := Airbender.NativeCallerPositionProofs.unique_count (Airbender.NativeTokenLedger.workerRows workers)
    Airbender.NativeActiveWorkerClocks.workerClock (fun w => w constraintsABI.multiplicity) clocks (Airbender.NativeActiveWorkerClocks.workerClock w)
  change Airbender.NativeActiveWorkerClocks.workerClock w ∈
    ((Airbender.NativeTokenLedger.workerRows workers).filter fun a => a constraintsABI.multiplicity = 1).map Airbender.NativeActiveWorkerClocks.workerClock at member
  rw [if_pos member] at one
  obtain ⟨source,qualifies,only⟩ := Airbender.NativeCallerPositionProofs.one_position _ _ _ _ one
  have equals : (Airbender.NativeTokenLedger.workerRows workers)[source.val] = w :=
    List.inj_on_of_nodup_map clocks (List.mem_filter.mpr ⟨List.getElem_mem source.isLt,by simpa using qualifies.2⟩)
      (List.mem_filter.mpr ⟨wm,by simpa using active⟩) qualifies.1
  refine ⟨source,⟨qualifies.2,by simpa only [equals] using same⟩,?_⟩
  intro other matched
  apply only other
  refine ⟨?_,matched.1⟩
  have clock := congrArg (fun e : Token × Token => e.2.time) (matched.2.symm.trans same)
  simpa only [Airbender.NativeActiveWorkerClockProofs.write_clock] using clock

theorem source_member {Setup R : Type} [Field R] {workers : WorkerBatch Setup R} {edge : Token × Token}
    {source : Fin (Airbender.NativeTokenLedger.workerRows workers).length} (matched : SourceAt workers edge source) : WorkerEdge workers edge :=
  ⟨_,List.getElem_mem source.isLt,matched⟩

theorem matching {Setup R : Type} [Field R] {proofs : List (Airbender.NativeInitializationBatch.Proof R)}
    {workers : WorkerBatch Setup R} {inputs : PublicBoundary} {path : List Token}
    (history : History proofs workers inputs path)
    (clocks : ((Airbender.NativeDelegationKeyAccounting.activeRows workers).map Airbender.NativeActiveWorkerClocks.workerClock).Nodup) :
    Matching workers path := by
  refine ⟨fun _ selected => source_unique clocks selected,?_⟩
  intro source active
  obtain ⟨index,equal⟩ := edge_position (history.workers _ (List.getElem_mem source.isLt) active)
  refine ⟨index,⟨active,equal⟩,?_⟩
  intro other matched
  exact edge_injective Airbender.NativeCompleteMemoryPaths.rank history.distinct (matched.2.trans equal.symm)


theorem segment_position {Setup R : Type} [Field R] {proofs : List (Airbender.NativeInitializationBatch.Proof R)}
    {workers : WorkerBatch Setup R} {inputs : PublicBoundary} {path : List Token}
    (history : History proofs workers inputs path) (target : Fin path.length) (start : Fin (target.val+1))
    {source : Fin (Airbender.NativeTokenLedger.workerRows workers).length}
    (present : SegmentSource workers path target start source) :
    ∃! index : Fin (target.val-start.val), SourceAt workers
      (edgeAt path target ⟨start.val + index.val,by have := index.isLt; omega⟩) source := by
  obtain ⟨index,matched⟩ := present
  refine ⟨index,matched,?_⟩
  intro other hm
  exact segment_injective Airbender.NativeCompleteMemoryPaths.rank history.distinct target start (hm.2.trans matched.2.symm)

theorem count_source {Setup R : Type} [Field R] {proofs : List (Airbender.NativeInitializationBatch.Proof R)}
    {workers : WorkerBatch Setup R} {inputs : PublicBoundary} {path : List Token}
    (history : History proofs workers inputs path)
    (clocks : ((Airbender.NativeDelegationKeyAccounting.activeRows workers).map Airbender.NativeActiveWorkerClocks.workerClock).Nodup)
    (target : Fin path.length) (start : Fin (target.val+1)) :
    workerCount workers path target start = sourceCount workers path target start := by
  classical
  rw [workerCount,flags_card]
  change Fintype.card {index // workerFlags workers path target start index = true} =
    Fintype.card {source // SegmentSource workers path target start source}
  apply matching_card (fun index source => SourceAt workers
    (edgeAt path target ⟨start.val + index.val.val,by have := index.val.isLt; omega⟩) source.val)
  · intro index
    obtain ⟨source,matched,only⟩ := source_unique clocks ((Airbender.NativeControlFoldProofs.flags_match workers path target start index.val).mp index.property)
    refine ⟨⟨source,index.val,matched⟩,matched,?_⟩
    intro other hm
    exact Subtype.ext (only other.val hm)
  · intro source
    obtain ⟨index,matched,only⟩ := segment_position history target start source.property
    have selected : workerFlags workers path target start index = true :=
      (Airbender.NativeControlFoldProofs.flags_match workers path target start index).mpr (source_member matched)
    refine ⟨⟨index,selected⟩,matched,?_⟩
    intro other hm
    exact Subtype.ext (only other.val hm)

theorem source_count_bound {Setup R : Type} [Field R] (workers : WorkerBatch Setup R)
    (path : List Token) (target : Fin path.length) (start : Fin (target.val+1)) :
    sourceCount workers path target start ≤ (Airbender.NativeTokenLedger.workerRows workers).length := by
  classical
  simpa only [sourceCount,Fintype.card_fin] using Fintype.card_subtype_le (SegmentSource workers path target start)


theorem source_fold {Setup R : Type} [Field R] {proofs : List (Airbender.NativeInitializationBatch.Proof R)}
    {workers : WorkerBatch Setup R} {inputs : PublicBoundary} {path : List Token}
    (history : History proofs workers inputs path)
    (clocks : ((Airbender.NativeDelegationKeyAccounting.activeRows workers).map Airbender.NativeActiveWorkerClocks.workerClock).Nodup)
    (target : Fin path.length) (start : Fin (target.val+1)) (fold : Fold workers path target start) :
    limbs (path.get target) = iterate advance (sourceCount workers path target start)
      (limbs (path.get ⟨start.val,by have := start.isLt; have := target.isLt; omega⟩)) := by
  simpa only [Fold,count_source history clocks target start] using fold

theorem from_prior {Setup R : Type} [Field R] {batch : Airbender.NativeMainDecoder.Batch R}
    {workers : WorkerBatch Setup R} {inputs : PublicBoundary} {before : Reference.RiscV.Sail.State}
    {publicSetup : SparseDecoderSetup Airbender.NativeCallerDecoder.Mode}
    (prior : Airbender.NativeControlFold.Effects before publicSetup batch workers inputs) :
    Airbender.NativeControlSource.Effects before publicSetup batch workers inputs := by
  have accounting : Airbender.NativeDelegationKeyAccounting.Effects batch workers inputs := prior.prior.prior.prior.prior.prior.prior.prior.prior.prior.prior.prior
  obtain ⟨path,history,origins,csr,arithmetic,bitwise,comparison,shifts,jumps,loads,results,positions⟩ := prior.path
  exact ⟨prior,path,history,origins,csr,arithmetic,bitwise,comparison,shifts,jumps,loads,results,positions,
    matching history accounting.clocksUnique,count_source history accounting.clocksUnique⟩

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
    (identity : Airbender.NativeDelegationSupport.SourceIdentity batch.main.proofs workers) :
    Airbender.NativeControlSource.Effects before publicSetup batch workers inputs :=
  from_prior (Airbender.NativeControlFoldProofs.counted publicSetup embed memory ch pc gamma decoder config accepted image lookups identity)
end Airbender.NativeControlSourceProofs
