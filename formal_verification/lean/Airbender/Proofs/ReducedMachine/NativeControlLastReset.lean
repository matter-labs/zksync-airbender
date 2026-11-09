import Airbender.Review.Trace.Families.ReducedMachine.ControlLastReset
import Airbender.Proofs.ReducedMachine.NativeControlLoad
import Mathlib.Data.Finset.Max

namespace Airbender.NativeControlLastResetProofs
open Airbender.NativeWorkerSnapshot Airbender.NativeControlHistory Airbender.NativeControlLogic
open Airbender.NativeControlLastReset Airbender.ReducedMachine Airbender.ReducedMachine.Native
open Airbender.Trace Airbender.Blake2Worker.Native Airbender.ReducedMachine.NativeMemoryBoundary
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

/-- Finite last-position selection is proved before any actual native data. -/
theorem last_position {n : Nat} (property : Fin n → Prop) :
    (∀ index, ¬ property index) ∨ ∃ last, property last ∧ ∀ index, last.val < index.val → ¬ property index := by
  classical
  by_cases present : ∃ index, property index
  · let selected := Finset.univ.filter property
    have nonempty : selected.Nonempty := by
      obtain ⟨index,holds⟩ := present
      exact ⟨index,Finset.mem_filter.mpr ⟨Finset.mem_univ _,holds⟩⟩
    let last := selected.max' nonempty
    have lm : last ∈ selected := Finset.max'_mem selected nonempty
    refine Or.inr ⟨last,(Finset.mem_filter.mp lm).2,?_⟩
    intro index later holds
    have im : index ∈ selected := Finset.mem_filter.mpr ⟨Finset.mem_univ _,holds⟩
    have before : index ≤ last := Finset.le_max' selected index im
    exact (not_lt_of_ge before) later
  · exact Or.inl (by intro index holds; exact present ⟨index,holds⟩)

theorem consecutive {A : Type} (path : List A) (index : Nat) (bound : index+1 < path.length) :
    (path[index]'(by omega),path[index+1]'bound) ∈ path.zip path.tail := by
  induction path generalizing index with
  | nil => simp at bound
  | cons first rest ih =>
    cases index with
    | zero =>
      cases rest with
      | nil => simp at bound
      | cons second tail => simp
    | succ index =>
      have shorter : index+1 < rest.length := by simpa using bound
      have member := ih index shorter
      cases rest with
      | nil => simp at shorter
      | cons second tail => exact List.mem_cons_of_mem _ member

theorem edge_member {A : Type} (path : List A) (target : Fin path.length) (index : Fin target.val) :
    edgeAt path target index ∈ path.zip path.tail := by
  exact consecutive path index.val (Nat.lt_of_le_of_lt (Nat.succ_le_of_lt index.isLt) target.isLt)

theorem member_position {A : Type} {path : List A} {token : A} (member : token ∈ path) :
    ∃ position : Fin path.length, path.get position = token := by
  induction path with
  | nil => simp at member
  | cons first rest ih =>
    rcases List.mem_cons.mp member with same | later
    · subst token; exact ⟨0,rfl⟩
    · obtain ⟨position,equal⟩ := ih later
      exact ⟨position.succ,equal⟩

/-- Bounded prefix induction, before any actual native data. -/
theorem prefix_induction {A : Type} (n : Nat) (value : Fin (n+1) → A) (property : A → Prop)
    (first : property (value 0))
    (steps : ∀ index : Fin n, property (value ⟨index.val,by omega⟩) → property (value ⟨index.val+1,by omega⟩)) :
    property (value ⟨n,by omega⟩) := by
  have all (index : Nat) (bound : index ≤ n) : property (value ⟨index,by omega⟩) := by
    induction index with
    | zero => exact first
    | succ index ih => exact steps ⟨index,by omega⟩ (ih (by omega))
  exact all n (le_refl _)

theorem head_position {A : Type} {path : List A} {token : A}
    (first : path.head? = some token) (positive : 0 < path.length) : path.get ⟨0,positive⟩ = token := by
  cases path with
  | nil => simp at positive
  | cons head tail => exact Option.some.inj first

theorem suffix_classified {Setup R : Type} [Field R] {proofs : List (Airbender.NativeInitializationBatch.Proof R)}
    {workers : WorkerBatch Setup R} {inputs : PublicBoundary} {path : List Token}
    (history : History proofs workers inputs path) {edge : Token × Token}
    (member : edge ∈ path.zip path.tail) (irrelevant : ¬ Relevant proofs edge) : WorkerOrCopy proofs workers edge := by
  rcases history.classified edge member with main | worker
  · left
    exact ⟨main,by by_contra changed; exact irrelevant ⟨main,changed⟩⟩
  · exact Or.inr worker

theorem seed_suffix_zero {Setup R : Type} [Field R] {proofs : List (Airbender.NativeInitializationBatch.Proof R)}
    {workers : WorkerBatch Setup R} {inputs : PublicBoundary} {path : List Token}
    (history : History proofs workers inputs path) (target : Fin path.length)
    (suffix : Suffix proofs workers path target 0) : limbs (path.get target) = (0,0) := by
  let value (index : Fin (target.val+1)) := path.get ⟨index.val,by have := index.isLt; have := target.isLt; omega⟩
  have first : limbs (value 0) = (0,0) := by
    change limbs (path.get ⟨0,by have := target.isLt; omega⟩) = _
    rw [head_position history.first,Airbender.NativeControlHistoryProofs.initial_zero]
  have steps (index : Fin target.val) (zero : limbs (value ⟨index.val,by omega⟩) = (0,0)) :
      limbs (value ⟨index.val+1,by omega⟩) = (0,0) := by
    change limbs (edgeAt path target index).1 = (0,0) at zero
    change limbs (edgeAt path target index).2 = (0,0)
    rcases (suffix index (Nat.zero_le _)).2 with copy | worker
    · exact (congrArg Nat.unpair copy.2).symm.trans zero
    · obtain ⟨w,wm,active,same,update⟩ := worker
      apply Prod.ext
      · exact update.1
      · exact Airbender.NativeControlOriginProofs.worker_zero _ update (congrArg Prod.snd zero)
  exact prefix_induction target.val value (fun token => limbs token = (0,0)) first steps

/-- A zero high limb cannot become nonzero inside the derived worker/copy suffix. -/
theorem suffix_high_zero {Setup R : Type} [Field R] {proofs : List (Airbender.NativeInitializationBatch.Proof R)}
    {workers : WorkerBatch Setup R} {path : List Token} (target : Fin path.length)
    (start : Fin (target.val+1)) (suffix : Suffix proofs workers path target start.val)
    (zero : (limbs (path.get ⟨start.val,by have := start.isLt; have := target.isLt; omega⟩)).2 = 0) :
    (limbs (path.get target)).2 = 0 := by
  let value (index : Fin (target.val-start.val+1)) :=
    path.get ⟨start.val + index.val,by have := index.isLt; have := start.isLt; have := target.isLt; omega⟩
  have first : (limbs (value 0)).2 = 0 := zero
  have steps (index : Fin (target.val-start.val)) (old : (limbs (value ⟨index.val,by omega⟩)).2 = 0) :
      (limbs (value ⟨index.val+1,by omega⟩)).2 = 0 := by
    let actual : Fin target.val := ⟨start.val + index.val,by have := index.isLt; omega⟩
    have left : value ⟨index.val,by omega⟩ = (edgeAt path target actual).1 := rfl
    have right : value ⟨index.val+1,by omega⟩ = (edgeAt path target actual).2 := by
      simp only [value,edgeAt,actual,Nat.add_assoc]
      rfl
    rw [left] at old
    rw [right]
    rcases (suffix actual (by simp only [actual]; omega)).2 with copy | worker
    · exact (congrArg (fun n => (Nat.unpair n).2) copy.2).symm.trans old
    · obtain ⟨w,wm,active,same,update⟩ := worker
      exact Airbender.NativeControlOriginProofs.worker_zero _ update old
  have result := prefix_induction (target.val-start.val) value (fun token => (limbs token).2 = 0) first steps
  have coordinate : start.val+(target.val-start.val) = target.val := by have := start.isLt; omega
  simpa only [value,coordinate] using result

theorem public_write {Setup R : Type} [Field R] {batch : Airbender.NativeMainDecoder.Batch R}
    {workers : WorkerBatch Setup R} {inputs : PublicBoundary} {path : List Token}
    {before : Reference.RiscV.Sail.State} {publicSetup : SparseDecoderSetup Airbender.NativeCallerDecoder.Mode}
    (history : History batch.main.proofs workers inputs path)
    (bodies : ∀ row ∈ Airbender.NativeMixedMemoryOrder.mainRows batch.main.proofs,
      FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment) (importedConstraints NativeRuntimePool.table))
    (sources : Airbender.NativeMainDecoder.PublicSources Airbender.NativeCallerDecoder.decoderFields before publicSetup batch)
    {edge : Token × Token} (member : edge ∈ path.zip path.tail) (relevant : Relevant batch.main.proofs edge) :
    PublicWrite before publicSetup batch.main.proofs edge := by
  obtain ⟨row,rm,present⟩ := relevant.1
  have third := Airbender.NativeControlOriginProofs.third_of_change present relevant.2
  have same : edge.1.address = address := of_decide_eq_true (List.mem_filter.mp (history.ports.mem_iff.mp member)).2
  obtain ⟨entry,em,source,query⟩ := Airbender.NativeControlOriginProofs.main_sources sources row rm
  have route : (Airbender.NativeMainDependencies.read row.assignment 2).address = address := by rwa [third] at same
  refine ⟨row,rm,entry,em,source,query,Airbender.NativeControlOriginProofs.public_rd (bodies row rm) source.fields query route,third,same,?_⟩
  intro nonzero
  apply Airbender.NativeControlCSRProofs.nonzero_source (bodies row rm) source.fields query
  simpa only [third] using nonzero

theorem outcome {Setup R : Type} [Field R] {batch : Airbender.NativeMainDecoder.Batch R}
    {workers : WorkerBatch Setup R} {inputs : PublicBoundary} {path : List Token}
    {before : Reference.RiscV.Sail.State} {publicSetup : SparseDecoderSetup Airbender.NativeCallerDecoder.Mode}
    (history : History batch.main.proofs workers inputs path)
    (bodies : ∀ row ∈ Airbender.NativeMixedMemoryOrder.mainRows batch.main.proofs,
      FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment) (importedConstraints NativeRuntimePool.table))
    (sources : Airbender.NativeMainDecoder.PublicSources Airbender.NativeCallerDecoder.decoderFields before publicSetup batch)
    (target : Fin path.length) : Outcome before publicSetup batch.main.proofs workers path target := by
  have classified (start : Nat) (none : ∀ index : Fin target.val, start ≤ index.val → ¬ Relevant batch.main.proofs (edgeAt path target index)) :
      Suffix batch.main.proofs workers path target start := by
    intro index later
    exact ⟨none index later,suffix_classified history (edge_member path target index) (none index later)⟩
  rcases last_position (fun index : Fin target.val => Relevant batch.main.proofs (edgeAt path target index)) with none | selected
  · have suffix := classified 0 (by intro index _; exact none index)
    exact Or.inl ⟨seed_suffix_zero history target suffix,suffix⟩
  · obtain ⟨index,relevant,last⟩ := selected
    have suffix := classified (index.val+1) (by intro later bound; exact last later (by omega))
    refine Or.inr ⟨index,relevant,public_write history bodies sources (edge_member path target index) relevant,?_,suffix⟩
    intro nonzero zero
    exact nonzero (suffix_high_zero target ⟨index.val+1,by have := index.isLt; omega⟩ suffix zero)

theorem nonzero_reset {Setup R : Type} [Field R] {proofs : List (Airbender.NativeInitializationBatch.Proof R)}
    {workers : WorkerBatch Setup R} {path : List Token} {target : Fin path.length}
    {before : Reference.RiscV.Sail.State} {publicSetup : SparseDecoderSetup Airbender.NativeCallerDecoder.Mode}
    (result : Outcome before publicSetup proofs workers path target) (nonzero : (limbs (path.get target)).2 ≠ 0) :
    ∃ index : Fin target.val, Relevant proofs (edgeAt path target index) ∧ PublicWrite before publicSetup proofs (edgeAt path target index) ∧
      (limbs (edgeAt path target index).2).2 ≠ 0 ∧ Suffix proofs workers path target (index.val+1) := by
  rcases result with seed | reset
  · exact False.elim (nonzero (congrArg Prod.snd seed.1))
  · obtain ⟨index,relevant,source,high,suffix⟩ := reset
    exact ⟨index,relevant,source,high nonzero,suffix⟩

theorem from_prior {Setup R : Type} [Field R] {batch : Airbender.NativeMainDecoder.Batch R}
    {workers : WorkerBatch Setup R} {inputs : PublicBoundary} {before : Reference.RiscV.Sail.State}
    {publicSetup : SparseDecoderSetup Airbender.NativeCallerDecoder.Mode}
    (prior : Airbender.NativeControlLoad.Effects before publicSetup batch workers inputs)
    (bodies : ∀ row ∈ Airbender.NativeMixedMemoryOrder.mainRows batch.main.proofs,
      FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment) (importedConstraints NativeRuntimePool.table))
    (sources : Airbender.NativeMainDecoder.PublicSources Airbender.NativeCallerDecoder.decoderFields before publicSetup batch) :
    Airbender.NativeControlLastReset.Effects before publicSetup batch workers inputs := by
  obtain ⟨path,history,origins,csr,arithmetic,bitwise,comparison,shifts,jumps,loads⟩ := prior.path
  have results := outcome history bodies sources
  refine ⟨prior,path,history,origins,csr,arithmetic,bitwise,comparison,shifts,jumps,loads,results,?_⟩
  intro w wm active
  obtain ⟨target,same⟩ := member_position (Airbender.NativeControlOriginProofs.zip_members (history.workers w wm active)).1
  exact ⟨target,same,results target⟩

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
    Airbender.NativeControlLastReset.Effects before publicSetup batch workers inputs := by
  have prior := Airbender.NativeControlLoadProofs.counted publicSetup embed memory ch pc gamma decoder config accepted image lookups identity
  have components := Airbender.NativeMemoryHistoryProofs.components embed memory ch pc gamma config accepted.counted.component
  have body := Airbender.NativeMainStateHistoryProofs.selected_body embed memory pc _ components
  have sources := Airbender.NativeMainDecoderProofs.public_sources publicSetup embed memory ch pc gamma decoder config accepted image lookups
  apply from_prior prior
  · intro row member
    have holds := body row member
    cases row with
    | mk family w => cases family; exact holds
  · exact sources
end Airbender.NativeControlLastResetProofs
