import Airbender.Review.Trace.Families.ReducedMachine.ControlFold
import Airbender.Proofs.ReducedMachine.NativeControlLastReset

namespace Airbender.NativeControlFoldProofs
open Airbender.NativeWorkerSnapshot Airbender.NativeControlHistory Airbender.NativeControlLogic
open Airbender.NativeControlLastReset Airbender.NativeControlFold
open Airbender.ReducedMachine Airbender.ReducedMachine.Native Airbender.Trace
open Airbender.Blake2Worker.Native Airbender.ReducedMachine.NativeMemoryBoundary
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

/-- Generic bounded-position fold, before actual native observations. -/
theorem selected_fold {A : Type} (step : A → A) (n : Nat) (value : Fin (n+1) → A) (flags : Fin n → Bool)
    (steps : ∀ index : Fin n, value ⟨index.val+1,by omega⟩ =
      if flags index then step (value ⟨index.val,by omega⟩) else value ⟨index.val,by omega⟩) :
    value ⟨n,by omega⟩ = iterate step (countFlags flags) (value 0) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have earlier := ih (fun index => value index.castSucc) (fun index => flags index.castSucc)
      (by intro index; exact steps index.castSucc)
    have lastStep := steps (Fin.last n)
    change value ⟨n+1,by omega⟩ = if flags (Fin.last n) then step (value ⟨n,by omega⟩) else value ⟨n,by omega⟩ at lastStep
    change value ⟨n,by omega⟩ = iterate step (countFlags (fun index => flags index.castSucc)) (value 0) at earlier
    rw [lastStep,earlier]
    cases flag : flags (Fin.last n) <;> simp only [countFlags,flag,Bool.false_eq_true,if_false,if_true,Nat.add_zero,Nat.add_one,iterate]

theorem count_bound (n : Nat) (flags : Fin n → Bool) : countFlags flags ≤ n := by
  induction n with
  | zero => exact le_refl 0
  | succ n ih =>
    have bound := ih (fun index => flags index.castSucc)
    cases flag : flags (Fin.last n) <;> simp only [countFlags,flag,Bool.false_eq_true,if_false,if_true] <;> omega

theorem count_none (n : Nat) : countFlags (fun _ : Fin n => false) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [countFlags,Bool.false_eq_true,if_false,Nat.add_zero] using ih

theorem count_all (n : Nat) : countFlags (fun _ : Fin n => true) = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [countFlags,if_true,ih]

theorem count_zero_iff (n : Nat) (flags : Fin n → Bool) : countFlags flags = 0 ↔ ∀ index, flags index = false := by
  induction n with
  | zero => exact ⟨by intro _ index; exact Fin.elim0 index,by intro _; rfl⟩
  | succ n ih =>
    constructor
    · intro zero
      have earlier : countFlags (fun index => flags index.castSucc) = 0 := by
        cases last : flags (Fin.last n) <;> simp only [countFlags,last,Bool.false_eq_true,if_false,if_true] at zero <;> omega
      have last : flags (Fin.last n) = false := by
        cases same : flags (Fin.last n)
        · rfl
        · simp only [countFlags,same,if_true] at zero; omega
      intro index
      by_cases small : index.val < n
      · have same : (⟨index.val,small⟩ : Fin n).castSucc = index := Fin.ext rfl
        rw [← same]
        exact (ih _).mp earlier ⟨index.val,small⟩
      · have same : index = Fin.last n := Fin.ext (by change index.val = n; have := index.isLt; omega)
        exact same ▸ last
    · intro none
      have earlier := (ih _).mpr (fun index => none index.castSucc)
      simp only [countFlags,earlier,none (Fin.last n),Bool.false_eq_true,if_false,Nat.add_zero]

theorem worker_updated {Setup R : Type} [Field R] {workers : WorkerBatch Setup R}
    (rows : ∀ w ∈ Airbender.NativeTokenLedger.workerRows workers, Airbender.NativeWorkerTransition.RowEffects w)
    {edge : Token × Token} (selected : WorkerEdge workers edge) : Updated edge := by
  obtain ⟨w,wm,_,rfl⟩ := selected
  exact Airbender.NativeControlHistoryProofs.updated (rows w wm)

theorem suffix_step {Setup R : Type} [Field R] {proofs : List (Airbender.NativeInitializationBatch.Proof R)}
    {workers : WorkerBatch Setup R} {path : List Token} (target : Fin path.length) (start : Fin (target.val+1))
    (rows : ∀ w ∈ Airbender.NativeTokenLedger.workerRows workers, Airbender.NativeWorkerTransition.RowEffects w)
    (suffix : Suffix proofs workers path target start.val) (index : Fin (target.val-start.val)) :
    limbs (edgeAt path target ⟨start.val + index.val,by have := index.isLt; omega⟩).2 =
      if workerFlags workers path target start index then
        advance (limbs (edgeAt path target ⟨start.val + index.val,by have := index.isLt; omega⟩).1)
      else limbs (edgeAt path target ⟨start.val + index.val,by have := index.isLt; omega⟩).1 := by
  classical
  let actual : Fin target.val := ⟨start.val + index.val,by have := index.isLt; omega⟩
  change limbs (edgeAt path target actual).2 = if decide (WorkerEdge workers (edgeAt path target actual)) then _ else _
  by_cases selected : WorkerEdge workers (edgeAt path target actual)
  · simp only [selected,decide_true,if_true]
    exact Prod.ext (worker_updated rows selected).1 (worker_updated rows selected).2
  · simp only [selected,decide_false]
    rcases (suffix actual (by simp only [actual]; omega)).2 with copy | worker
    · exact (congrArg Nat.unpair copy.2).symm
    · obtain ⟨w,wm,active,same,_⟩ := worker
      exact False.elim (selected ⟨w,wm,active,same⟩)

theorem suffix_fold {Setup R : Type} [Field R] {proofs : List (Airbender.NativeInitializationBatch.Proof R)}
    {workers : WorkerBatch Setup R} {path : List Token} (target : Fin path.length) (start : Fin (target.val+1))
    (rows : ∀ w ∈ Airbender.NativeTokenLedger.workerRows workers, Airbender.NativeWorkerTransition.RowEffects w)
    (suffix : Suffix proofs workers path target start.val) : Fold workers path target start := by
  let value (index : Fin (target.val-start.val+1)) :=
    limbs (path.get ⟨start.val + index.val,by have := index.isLt; have := start.isLt; have := target.isLt; omega⟩)
  have steps (index : Fin (target.val-start.val)) : value ⟨index.val+1,by omega⟩ =
      if workerFlags workers path target start index then advance (value ⟨index.val,by omega⟩) else value ⟨index.val,by omega⟩ := by
    have result := suffix_step target start rows suffix index
    simpa only [value,edgeAt,Nat.add_assoc,List.get_eq_getElem] using result
  have result := selected_fold advance (target.val-start.val) value (workerFlags workers path target start) steps
  have coordinate : start.val+(target.val-start.val) = target.val := by have := start.isLt; omega
  simpa only [Fold,workerCount,value,coordinate,Fin.val_zero,Nat.add_zero,List.get_eq_getElem] using result

theorem flags_match {Setup R : Type} [Field R] (workers : WorkerBatch Setup R)
    (path : List Token) (target : Fin path.length) (start : Fin (target.val+1)) (index : Fin (target.val-start.val)) :
    workerFlags workers path target start index = true ↔
      WorkerEdge workers (edgeAt path target ⟨start.val + index.val,by have := index.isLt; omega⟩) := by
  classical
  simp only [workerFlags,decide_eq_true_eq]

theorem worker_count_bound {Setup R : Type} [Field R] (workers : WorkerBatch Setup R)
    (path : List Token) (target : Fin path.length) (start : Fin (target.val+1)) :
    workerCount workers path target start ≤ target.val-start.val := count_bound _ _

theorem worker_count_zero_iff {Setup R : Type} [Field R] (workers : WorkerBatch Setup R)
    (path : List Token) (target : Fin path.length) (start : Fin (target.val+1)) :
    workerCount workers path target start = 0 ↔ ∀ index : Fin (target.val-start.val),
      ¬ WorkerEdge workers (edgeAt path target ⟨start.val + index.val,by have := index.isLt; omega⟩) := by
  classical
  rw [workerCount,count_zero_iff]
  simp only [workerFlags,decide_eq_false_iff_not]

theorem no_worker_copy {Setup R : Type} [Field R] {workers : WorkerBatch Setup R}
    {path : List Token} {target : Fin path.length} {start : Fin (target.val+1)}
    (result : Fold workers path target start) (zero : workerCount workers path target start = 0) :
    limbs (path.get target) = limbs (path.get ⟨start.val,by have := start.isLt; have := target.isLt; omega⟩) := by
  simpa only [Fold,zero,iterate] using result

theorem outcome {Setup R : Type} [Field R] {proofs : List (Airbender.NativeInitializationBatch.Proof R)}
    {workers : WorkerBatch Setup R} {path : List Token} {target : Fin path.length}
    {before : Reference.RiscV.Sail.State} {publicSetup : SparseDecoderSetup Airbender.NativeCallerDecoder.Mode}
    (rows : ∀ w ∈ Airbender.NativeTokenLedger.workerRows workers, Airbender.NativeWorkerTransition.RowEffects w)
    (prior : Airbender.NativeControlLastReset.Outcome before publicSetup proofs workers path target) :
    Airbender.NativeControlFold.Outcome before publicSetup proofs workers path target := by
  rcases prior with seed | reset
  · exact Or.inl ⟨seed.1,seed.2,suffix_fold target 0 rows seed.2⟩
  · obtain ⟨index,relevant,source,high,suffix⟩ := reset
    exact Or.inr ⟨index,relevant,source,high,suffix,suffix_fold target ⟨index.val+1,by have := index.isLt; omega⟩ rows suffix⟩

theorem from_prior {Setup R : Type} [Field R] {batch : Airbender.NativeMainDecoder.Batch R}
    {workers : WorkerBatch Setup R} {inputs : PublicBoundary} {before : Reference.RiscV.Sail.State}
    {publicSetup : SparseDecoderSetup Airbender.NativeCallerDecoder.Mode}
    (prior : Airbender.NativeControlLastReset.Effects before publicSetup batch workers inputs) :
    Airbender.NativeControlFold.Effects before publicSetup batch workers inputs := by
  have joint : Airbender.NativeJointReplay.Effects batch workers inputs := prior.prior.prior.prior.prior.prior.prior.prior.prior.prior.prior.prior
  have rows := joint.prior.prior.transitions
  obtain ⟨path,history,origins,csr,arithmetic,bitwise,comparison,shifts,jumps,loads,results,positions⟩ := prior.path
  refine ⟨prior,path,history,origins,csr,arithmetic,bitwise,comparison,shifts,jumps,loads,?_,?_⟩
  · intro target; exact outcome rows (results target)
  · intro w wm active
    obtain ⟨target,same,result⟩ := positions w wm active
    exact ⟨target,same,outcome rows result⟩

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
    Airbender.NativeControlFold.Effects before publicSetup batch workers inputs :=
  from_prior (Airbender.NativeControlLastResetProofs.counted publicSetup embed memory ch pc gamma decoder config accepted image lookups identity)
end Airbender.NativeControlFoldProofs
