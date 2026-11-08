import Airbender.Review.Trace.Families.ReducedMachine.DelegationKeyAccounting
import Airbender.Proofs.ReducedMachine.NativeJointReplay
namespace Airbender.NativeDelegationKeyAccountingProofs
open Airbender.NativeDelegationSupport
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

theorem picks_sublist {A E : Type} (items : List A) (enabled : A → Bool)
    (ports : A → List E) (pick : A → E)
    (present : ∀ item ∈ items, enabled item = true → pick item ∈ ports item) :
    ((items.filter enabled).map pick).Sublist
      (items.flatMap fun item => if enabled item then ports item else []) := by
  induction items with
  | nil => exact .slnil
  | cons first tail ih =>
    have next := ih (fun item member => present item (List.mem_cons_of_mem _ member))
    cases h : enabled first with
    | false => simpa [h] using next
    | true =>
      have head : [pick first].Sublist (ports first) := List.singleton_sublist.mpr (present first (by simp) h)
      simpa [h] using head.append next

theorem nodup_keys {A K V : Type} (items : List A) (key : A → K) (value : A → V)
    (unique : (items.map value).Nodup)
    (same : ∀ a ∈ items, ∀ b ∈ items, key a = key b → value a = value b) :
    (items.map key).Nodup := by
  induction items with
  | nil => exact .nil
  | cons first tail ih =>
    have old := List.nodup_cons.mp unique
    apply List.nodup_cons.mpr
    constructor
    · intro member
      obtain ⟨item,member,equal⟩ := List.mem_map.mp member
      apply old.1
      exact List.mem_map.mpr ⟨item,member,same item (by simp [member]) first (by simp) equal⟩
    · exact ih old.2 (fun a am b bm => same a (by simp [am]) b (by simp [bm]))

/-- Boolean weights with unique active keys have an exact 0/1 coefficient.
    Zero rows and every original list occurrence remain in weightAt. -/
theorem unique_weight {A K : Type} [DecidableEq K] (items : List A)
    (key : A → K) (weight : A → F)
    (boolean : ∀ item ∈ items, weight item = 0 ∨ weight item = 1)
    (unique : ((items.filter fun item => weight item = 1).map key).Nodup) (target : K) :
    weightAt items key weight target =
      if target ∈ (items.filter fun item => weight item = 1).map key then 1 else 0 := by
  induction items with
  | nil => simp [weightAt]
  | cons first tail ih =>
    have bit := boolean first (by simp)
    have next := ih (fun item member => boolean item (by simp [member]))
    rcases bit with zero | one
    · have different : weight first ≠ 1 := by rw [zero]; exact zero_ne_one
      have restUnique : ((tail.filter fun item => weight item = 1).map key).Nodup := by
        simpa [different] using unique
      have result := next restUnique
      have selected : ((first :: tail).filter fun item => weight item = 1).map key =
          (tail.filter fun item => weight item = 1).map key := by simp [different]
      rw [selected]
      by_cases equal : key first = target <;> simpa [weightAt,zero,equal] using result
    · have restUnique : ((tail.filter fun item => weight item = 1).map key).Nodup :=
        (List.nodup_cons.mp (by simpa [one] using unique)).2
      have absent : key first ∉ (tail.filter fun item => weight item = 1).map key :=
        (List.nodup_cons.mp (by simpa [one] using unique)).1
      have result := next restUnique
      have selected : ((first :: tail).filter fun item => weight item = 1).map key =
          key first :: (tail.filter fun item => weight item = 1).map key := by simp [one]
      rw [selected]
      by_cases equal : key first = target
      · rw [equal] at absent
        simp [weightAt,one,equal,absent] at result ⊢
        exact result
      · have reverse : target ≠ key first := Ne.symm equal
        simp only [List.mem_cons,reverse,false_or]
        simpa [weightAt,equal] using result
theorem absent_weight {A K : Type} [DecidableEq K] (items : List A) (key : A → K)
    (weight : A → F) (target : K) (absent : target ∉ items.map key) : weightAt items key weight target = 0 := by
  induction items with
  | nil => simp [weightAt]
  | cons first tail ih =>
    have head : key first ≠ target := by intro same; exact absent (by simp [same])
    have rest : target ∉ tail.map key := fun member => absent (List.mem_cons_of_mem _ member)
    simpa [weightAt,head] using ih rest

theorem coefficient_all {callers workers : List (Nat → F)} (identity : FormalIdentity callers workers) (target : Key) :
    weightAt callers callerKey (fun w => w 92) target =
      weightAt workers workerKey (fun w => w Airbender.Blake2Worker.Native.constraintsABI.multiplicity) target := by
  by_cases member : target ∈ poles callers workers
  · exact Airbender.NativeDelegationSupportProofs.coefficient_balance identity member
  · have left : target ∉ callers.map callerKey := by
      intro present; apply member
      exact Finset.mem_union_left _ (List.mem_toFinset.mpr present)
    have right : target ∉ workers.map workerKey := by
      intro present; apply member
      exact Finset.mem_union_right _ (List.mem_toFinset.mpr present)
    rw [absent_weight callers callerKey _ target left,absent_weight workers workerKey _ target right]

open Airbender.NativeDelegationKeyAccounting Airbender.Blake2Worker.Native
open Airbender.NativeWorkerSnapshot (read write)
open Airbender.ReducedMachine.Native Airbender.Trace Airbender.Verification
open Airbender.ReducedMachine.NativeMemoryBoundary

theorem control_descriptor : (keyDescriptor (42 : Fin 43)).location = .register 12 := by decide +kernel

theorem control_address (w : Nat → F) : (write w 42).address = Nat.pair 0 (Nat.pair 12 0) := by
  change Airbender.NativeMemoryTokens.encodeAddress (quotientKeyAddress w (keyDescriptor 42).location) = _
  rw [control_descriptor]
  rfl

theorem active_clocks {Setup R : Type} [Field R]
    {proofs : List (Airbender.NativeInitializationBatch.Proof R)} {workers : WorkerBatch Setup R} {inputs : PublicBoundary}
    (unique : Airbender.NativeMemoryWriteUniqueness.Effects proofs workers inputs) :
    ((activeRows workers).map Airbender.NativeActiveWorkerClocks.workerClock).Nodup := by
  have selected := picks_sublist (Airbender.NativeTokenLedger.workerRows workers)
    (fun w => decide (w constraintsABI.multiplicity = 1)) Airbender.NativeMemoryRoots.workerSteps
    (fun w => (read w 42,write w 42))
    (fun w _ _ => Airbender.NativeWorkerGroupProofs.port_member w 42)
  have whole : ((activeRows workers).map fun w => (read w 42,write w 42)).Sublist
      (Airbender.NativeMemoryRoots.steps proofs workers) := by
    change ((activeRows workers).map fun w => (read w 42,write w 42)).Sublist
      ((Airbender.NativeMixedMemoryOrder.mainRows proofs).flatMap Trace.Row.memorySteps ++
        (Airbender.NativeTokenLedger.workerRows workers).flatMap fun w =>
          if w constraintsABI.multiplicity = 1 then Airbender.NativeMemoryRoots.workerSteps w else [])
    apply List.Sublist.trans _ (List.sublist_append_right _ _)
    simpa only [activeRows,decide_eq_true_eq] using selected
  have distinct := unique.writes.sublist (whole.map (fun edge => Airbender.NativeMemoryWriteUniqueness.writeKey edge.2))
  have mapped : ((activeRows workers).map fun w => Airbender.NativeMemoryWriteUniqueness.writeKey (write w 42)).Nodup := by
    simpa only [List.map_map,Function.comp_def] using distinct
  apply nodup_keys (activeRows workers) Airbender.NativeActiveWorkerClocks.workerClock _ mapped
  intro a _ b _ same
  apply Prod.ext
  · change (write a 42).address = (write b 42).address
    rw [control_address,control_address]
  · unfold Airbender.NativeMemoryWriteUniqueness.writeKey Airbender.NativeCompleteMemoryPaths.rank
    rw [Airbender.NativeActiveWorkerClockProofs.write_clock,Airbender.NativeActiveWorkerClockProofs.write_clock,same]

theorem active_keys {Setup R : Type} [Field R] (workers : WorkerBatch Setup R)
    (unique : ((activeRows workers).map Airbender.NativeActiveWorkerClocks.workerClock).Nodup) : (keys workers).Nodup := by
  apply nodup_keys (activeRows workers) workerKey Airbender.NativeActiveWorkerClocks.workerClock unique
  intro a _ b _ same
  exact Prod.ext (congrArg CSRArgumentKey.low same) (congrArg CSRArgumentKey.high same)

theorem accounting {Setup R : Type} [Field R]
    {batch : Airbender.NativeMainDecoder.Batch R} {workers : WorkerBatch Setup R} {inputs : PublicBoundary}
    (prior : Airbender.NativeJointReplay.Effects batch workers inputs)
    (boolean : ∀ w ∈ Airbender.NativeTokenLedger.workerRows workers,
      w constraintsABI.multiplicity = 0 ∨ w constraintsABI.multiplicity = 1)
    (identity : SourceIdentity batch.main.proofs workers) : Airbender.NativeDelegationKeyAccounting.Effects batch workers inputs := by
  have clocks := active_clocks prior.prior.prior.prior.words.prior.workers.prior.latest.unique
  have distinct := active_keys workers clocks
  have worker : ∀ target, workerWeight workers target = if target ∈ keys workers then 1 else 0 :=
    unique_weight (Airbender.NativeTokenLedger.workerRows workers) workerKey _ boolean distinct
  have caller : ∀ target, callerWeight batch.main.proofs target = if target ∈ keys workers then 1 else 0 := by
    intro target
    exact (coefficient_all identity target).trans (worker target)
  refine ⟨prior,clocks,distinct,worker,caller,?_,?_,?_⟩
  · intro target
    rw [caller target]
    by_cases member : target ∈ keys workers <;> simp [member]
  · intro target
    rw [caller target]
    by_cases member : target ∈ keys workers <;> simp [member]
  · intro a am b bm same
    exact List.inj_on_of_nodup_map distinct am bm same

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
    (identity : Airbender.NativeDelegationSupport.SourceIdentity batch.main.proofs workers) : Airbender.NativeDelegationKeyAccounting.Effects batch workers inputs := by
  have prior := Airbender.NativeJointReplayProofs.counted publicSetup embed memory ch pc gamma decoder config accepted image lookups identity
  have processing := Airbender.NativeActiveWorkerClockProofs.worker_processing embed memory ch pc gamma config accepted.counted.component
  have boolean : ∀ w ∈ Airbender.NativeTokenLedger.workerRows workers,
      w constraintsABI.multiplicity = 0 ∨ w constraintsABI.multiplicity = 1 := by
    intro w member
    exact (Airbender.Blake2Worker.ProcessingProofs.effects (processing w member).conventions).multiplicityBit
  exact accounting prior boolean identity
end Airbender.NativeDelegationKeyAccountingProofs
