import Airbender.Review.Trace.Families.ReducedMachine.WorkerSeed
import Airbender.Proofs.ReducedMachine.NativeAddressSupport
import Airbender.Proofs.ReducedMachine.NativeDelegationKeyAccounting
import Airbender.Proofs.ReducedMachine.NativeSparseMain
import Airbender.Proofs.ReducedMachine.NativeInactiveGlobal

namespace Airbender.NativeWorkerSeedProofs
open Airbender.NativeWorkerSeed
open Airbender.Blake2Worker.Native Airbender.ReducedMachine.NativeMemoryBoundary
open Airbender.ReducedMachine.Native Airbender.NativeDelegationSupport
private abbrev F := ZMod mersenne31Modulus
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

theorem ram_descriptor : (keyDescriptor (1 : Fin 43)).location = .indirect #v[2,3] 0 := by decide +kernel

theorem ram_space (w : Nat → F) :
    (Nat.unpair (Airbender.NativeWorkerClockProgress.readToken w 1).address).1 = 1 := by
  simp [Airbender.NativeWorkerClockProgress.readToken,Airbender.NativeMemoryTokens.encodeKey,
    quotientMemoryKey,ram_descriptor,quotientKeyAddress,Airbender.NativeMemoryTokens.encodeAddress]
  change (1 : F).val = 1
  decide +kernel

theorem register_space (index : BitVec 5) :
    (Nat.unpair (Trace.Cell.register index).addressCode).1 = 0 := by
  simp [Trace.Cell.addressCode]

theorem ram_source {R : Type} [Field R] {proofs : List (Airbender.NativeInitializationBatch.Proof R)}
    {cell : Trace.Cell} (member : cell ∈ Airbender.NativeInitializationSeedBoundary.cells proofs)
    (ram : (Nat.unpair cell.addressCode).1 = 1) :
    ∃ w ∈ callerRows proofs, Airbender.NativeInitializationLedger.paddingRow w = false := by
  rcases List.mem_append.mp member with reg | memory
  · obtain ⟨index,_,same⟩ := List.mem_map.mp reg
    subst cell
    rw [register_space] at ram
    contradiction
  · obtain ⟨token,tm,_⟩ := List.mem_map.mp memory
    obtain ⟨w,wm,_⟩ := List.mem_map.mp tm
    have present := List.mem_filter.mp wm
    refine ⟨w,present.1,?_⟩
    cases flag : Airbender.NativeInitializationLedger.paddingRow w <;> simp_all

theorem active_requires_seed {Setup R : Type} [Field R] (embed : F →+* R) (memory : MemoryKeyChallenges R)
    (ch : CSRArgumentChallenges R) (pc : PCChallenges R) (gamma : R) (config : WorkerConfiguration Setup)
    {proofs : List (Airbender.NativeInitializationBatch.Proof R)} {workers : WorkerBatch Setup R}
    {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : Airbender.NativeInitializationBatch.Accepted embed memory ch pc gamma config proofs workers inputs inverse)
    (identity : SourceIdentity proofs workers) {w : Nat → F}
    (member : w ∈ Airbender.NativeTokenLedger.workerRows workers) (active : w constraintsABI.multiplicity = 1) :
    ∃ source ∈ callerRows proofs, Airbender.NativeInitializationLedger.paddingRow source = false := by
  have support := Airbender.NativeAddressSupportProofs.effects embed memory ch pc gamma config accepted identity
  obtain ⟨cell,present,address,_⟩ := support.cells _ _ (Or.inr ⟨w,member,active,1,rfl,rfl⟩)
  apply ram_source present
  rw [← address]
  exact ram_space w

/-- Full positional weight, before native rows/domains. -/
theorem spike_weight {I A K : Type} [DecidableEq I] [DecidableEq K]
    (items : List I) (position : I) (positive idle : A) (key : A → K) (weight : A → F)
    (one : weight positive = 1) (zero : weight idle = 0) :
    weightAt (items.map fun i => if i = position then positive else idle) key weight (key positive) =
      (items.count position : F) := by
  induction items with
  | nil => simp [weightAt]
  | cons i items ih =>
    simp only [weightAt] at ih
    by_cases selected : i = position <;> by_cases same : key idle = key positive
    all_goals simp [weightAt,selected,same,one,zero,ih,add_comm]

theorem append_weight {A K : Type} [DecidableEq K] (left right : List A)
    (key : A → K) (weight : A → F) (target : K) :
    weightAt (left ++ right) key weight target = weightAt left key weight target + weightAt right key weight target := by
  simp [weightAt]

theorem repeated_weight {A K : Type} [DecidableEq K] (items : List A) (n : Nat)
    (key : A → K) (weight : A → F) (target : K) :
    weightAt ((List.replicate n items).flatten) key weight target = (n : F)*weightAt items key weight target := by
  induction n with
  | zero => simp [weightAt]
  | succ n ih => simp [List.replicate_succ,append_weight,ih,Nat.cast_add,Nat.cast_one,add_mul,add_comm]

theorem zero_weight {A K : Type} [DecidableEq K] (items : List A) (key : A → K)
    (weight : A → F) (target : K) (zero : ∀ item ∈ items, weight item = 0) :
    weightAt items key weight target = 0 := by
  apply List.sum_eq_zero
  intro value member
  obtain ⟨item,present,rfl⟩ := List.mem_map.mp member
  exact zero item (List.mem_of_mem_filter present)

open Airbender.ReducedMachine.NativeMainAuxiliary Airbender.ReducedMachine
open Airbender.NativeSparseMain

theorem source_weight (position : Fin (callerAuxiliaryLayout.traceLength-1)) :
    weightAt ((List.range (callerAuxiliaryLayout.traceLength-1)).map (rows NativeSparseMainProofs.original position))
      callerKey (fun w => w 92) (callerKey NativeSparseMainProofs.original) = 1 := by
  have sum := spike_weight (List.range (callerAuxiliaryLayout.traceLength-1)) position.val
    NativeSparseMainProofs.original NativeSparseMainProofs.idle callerKey (fun w => w 92)
    (by decide +kernel) (by decide +kernel)
  have count : (List.range (callerAuxiliaryLayout.traceLength-1)).count position.val = 1 :=
    List.count_eq_one_of_mem List.nodup_range (List.mem_range.mpr position.isLt)
  change weightAt ((List.range (callerAuxiliaryLayout.traceLength-1)).map fun i =>
    if i = position.val then NativeSparseMainProofs.original else NativeSparseMainProofs.idle) _ _ _ = 1
  simpa only [count,Nat.cast_one] using sum

/-- Every actual sparse source row has ALL six padding fields zero. -/
theorem source_padding (position : Fin (callerAuxiliaryLayout.traceLength-1)) (i : Nat) :
    Airbender.NativeInitializationLedger.paddingRow (rows NativeSparseMainProofs.original position i) = true := by
  unfold rows
  split
  all_goals
    apply List.all_eq_true.mpr
    intro column member
    simp only [decide_eq_true_eq]
  · exact NativeSparseMainProofs.original_padding column member
  · exact NativeSparseMainProofs.idle_padding column member

theorem copy_padding {R : Type} [Field R] (proof : Airbender.NativeMainDecoder.Proof R) (countWord : BitVec 32)
    (position : Fin (callerAuxiliaryLayout.traceLength-1))
    (same : proof.initialization.main.memory.rows = rows NativeSparseMainProofs.original position) :
    ∀ w ∈ callerRows (Airbender.NativeInactiveGlobal.copies proof countWord).main.proofs,
      Airbender.NativeInitializationLedger.paddingRow w = true := by
  intro w member
  obtain ⟨p,pm,wm⟩ := List.mem_flatMap.mp member
  obtain ⟨i,_,wi⟩ := List.mem_map.mp wm
  obtain ⟨source,sm,ps⟩ := List.mem_map.mp pm
  rw [Airbender.NativeInactiveGlobalProofs.copy_proofs] at sm
  have sourceSame : source = proof.initialization := (List.mem_replicate.mp sm).2
  subst source
  subst p
  rw [← wi,congrFun same i]
  exact source_padding position i

theorem copy_weight {R : Type} [Field R] (proof : Airbender.NativeMainDecoder.Proof R) (countWord : BitVec 32)
    (position : Fin (callerAuxiliaryLayout.traceLength-1))
    (same : proof.initialization.main.memory.rows = rows NativeSparseMainProofs.original position) :
    Airbender.NativeDelegationKeyAccounting.callerWeight (Airbender.NativeInactiveGlobal.copies proof countWord).main.proofs
      (callerKey NativeSparseMainProofs.original) = (countWord.toNat : F) := by
  change weightAt ((Airbender.NativeInitializationBatch.mainProofs
    (Airbender.NativeInactiveGlobal.copies proof countWord).main.proofs).flatMap
      (fun (p : MainProof R) => (List.range (callerAuxiliaryLayout.traceLength-1)).map p.rows)) _ _ _ = _
  rw [Airbender.NativeInitializationBatch.mainProofs,Airbender.NativeInactiveGlobalProofs.copy_proofs]
  simp only [List.map_replicate,List.flatMap_replicate,same]
  rw [repeated_weight,source_weight,mul_one]

/-- Full global acceptance forces every worker multiplicity to zero when the
    actual initialization source has only six-field padding records. -/
theorem padding_workers_zero {Setup R : Type} [Field R] (embed : F →+* R) (memory : MemoryKeyChallenges R)
    (ch : CSRArgumentChallenges R) (pc : PCChallenges R) (gamma : R) (config : WorkerConfiguration Setup)
    {proofs : List (Airbender.NativeInitializationBatch.Proof R)} {workers : WorkerBatch Setup R}
    {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : Airbender.NativeInitializationBatch.Accepted embed memory ch pc gamma config proofs workers inputs inverse)
    (identity : SourceIdentity proofs workers)
    (padding : ∀ source ∈ callerRows proofs, Airbender.NativeInitializationLedger.paddingRow source = true) :
    ∀ w ∈ Airbender.NativeTokenLedger.workerRows workers, w constraintsABI.multiplicity = 0 := by
  have processing := Airbender.NativeActiveWorkerClockProofs.worker_processing embed memory ch pc gamma config accepted
  intro w member
  rcases (Airbender.Blake2Worker.ProcessingProofs.effects (processing w member).conventions).multiplicityBit with zero | active
  · exact zero
  · obtain ⟨source,present,nonpadding⟩ := active_requires_seed embed memory ch pc gamma config accepted identity member active
    rw [padding source present] at nonpadding
    contradiction

theorem reject_sparse {Kind Setup R : Type} [Field R]
    (publicSetup : Airbender.Trace.SparseDecoderSetup Kind)
    (embed : F →+* R) (memory : MemoryKeyChallenges R) (ch : CSRArgumentChallenges R)
    (pc : PCChallenges R) (gamma : R) (decoder : NativeDecoderArguments.Challenges R) (config : WorkerConfiguration Setup)
    (proof : Airbender.NativeMainDecoder.Proof R) (countWord : BitVec 32)
    (position : Fin (callerAuxiliaryLayout.traceLength-1))
    (same : proof.initialization.main.memory.rows = rows NativeSparseMainProofs.original position)
    {workers : WorkerBatch Setup R} {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : Airbender.NativeMainDecoder.SourceAccepted publicSetup embed memory ch pc gamma decoder config
      (Airbender.NativeInactiveGlobal.copies proof countWord) workers inputs inverse)
    (identity : SourceIdentity (Airbender.NativeInactiveGlobal.copies proof countWord).main.proofs workers) : False := by
  have zero := padding_workers_zero embed memory ch pc gamma config accepted.counted.component identity
    (copy_padding proof countWord position same)
  have coefficient := Airbender.NativeDelegationKeyAccountingProofs.coefficient_all identity (callerKey NativeSparseMainProofs.original)
  rw [zero_weight _ _ _ _ zero] at coefficient
  change Airbender.NativeDelegationKeyAccounting.callerWeight _ _ = 0 at coefficient
  rw [copy_weight proof countWord position same] at coefficient
  have limits := (Airbender.NativeMainBatchProofs.counter_iff _).mp accepted.counted.counter
  change 0 < countWord.toNat ∧ countWord.toNat ≤ 8192 at limits
  have canonical : (countWord.toNat : F).val = countWord.toNat := ZMod.val_natCast_of_lt (by change countWord.toNat < 2147483647; omega)
  have value := congrArg ZMod.val coefficient
  rw [canonical] at value
  change countWord.toNat = 0 at value
  omega


theorem withMain_memory {R : Type} [Field R] (main : NativeMainArguments.Proof R) (proof : Airbender.NativeMainDecoder.Proof R) :
    (withMain main proof).initialization.main = main := rfl

theorem withMain_scalar {R : Type} [Field R] (main : NativeMainArguments.Proof R) (proof : Airbender.NativeMainDecoder.Proof R) :
    (withMain main proof).initialization.base = proof.initialization.base ∧
    (withMain main proof).initialization.witness = proof.initialization.witness ∧
    (withMain main proof).initialization.setup = proof.initialization.setup ∧
    (withMain main proof).initialization.scalarPolynomial = proof.initialization.scalarPolynomial ∧
    (withMain main proof).initialization.scalarOmega = proof.initialization.scalarOmega ∧
    (withMain main proof).initialization.values = proof.initialization.values := by exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem withMain_decoder {R : Type} [Field R] (main : NativeMainArguments.Proof R) (proof : Airbender.NativeMainDecoder.Proof R) :
    (withMain main proof).witness = proof.witness ∧ (withMain main proof).setup = proof.setup ∧
    (withMain main proof).polynomial = proof.polynomial ∧ (withMain main proof).omega = proof.omega := by exact ⟨rfl,rfl,rfl,rfl⟩

theorem constructed_rejection {Kind Setup R : Type} [Field R]
    (publicSetup : Airbender.Trace.SparseDecoderSetup Kind)
    (embed : F →+* R) (memory : MemoryKeyChallenges R) (pc : PCChallenges R) (ch : CSRArgumentChallenges R)
    (decoder : NativeDecoderArguments.Challenges R) (gamma : R) (config : WorkerConfiguration Setup)
    (position : Fin (callerAuxiliaryLayout.traceLength-1))
    (nonpoles : Airbender.NativeInactiveMain.Nonpoles embed memory pc ch NativeSparseMainProofs.original)
    (omega : R) (primitive : IsPrimitiveRoot omega callerAuxiliaryLayout.traceLength) :
    ∃ main : NativeMainArguments.Proof R,
      (main.memory.rows = rows NativeSparseMainProofs.original position ∧ main.memory.grandClaim = 1 ∧
       Accepted embed memory pc main.memory ∧ CallerDelegationAccepted embed ch main.caller ∧
       (∀ i < callerAuxiliaryLayout.traceLength-1, NativeDecoderArguments.RowAccepted embed decoder (main.memory.rows i) (main.memory.auxiliary i)) ∧
       main.delegationClaim = (csrStageThreeArgument embed ch 1 NativeSparseMainProofs.original)⁻¹ ∧ main.delegationClaim ≠ 0) ∧
      ∀ surrounding : Airbender.NativeMainDecoder.Proof R, ∀ countWord : BitVec 32,
        ∀ workers : WorkerBatch Setup R, ∀ inputs : PublicBoundary, ∀ inverse : BoundaryInverses R,
        ¬ (Airbender.NativeMainDecoder.SourceAccepted publicSetup embed memory ch pc gamma decoder config
          (Airbender.NativeInactiveGlobal.copies (withMain main surrounding) countWord) workers inputs inverse ∧
          SourceIdentity (Airbender.NativeInactiveGlobal.copies (withMain main surrounding) countWord).main.proofs workers) := by
  obtain ⟨main,components⟩ := NativeSparseMainProofs.complete embed memory pc ch decoder position nonpoles omega primitive
  refine ⟨main,components,?_⟩
  intro surrounding countWord workers inputs inverse
  rintro ⟨accepted,identity⟩
  exact reject_sparse publicSetup embed memory ch pc gamma decoder config (withMain main surrounding) countWord position
    components.1 accepted identity

end Airbender.NativeWorkerSeedProofs



