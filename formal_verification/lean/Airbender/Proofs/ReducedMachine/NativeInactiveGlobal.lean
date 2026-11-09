import Airbender.Review.Trace.Families.ReducedMachine.InactiveGlobal
import Airbender.Proofs.ReducedMachine.NativeDelegationKeyAccounting
import Airbender.Proofs.ReducedMachine.NativeCallerCount
import Airbender.Proofs.ReducedMachine.NativeInitializationComponent

namespace Airbender.NativeInactiveGlobalProofs
open Airbender.NativeInactiveGlobal Airbender.NativeDelegationSupport
abbrev F := ZMod mersenne31Modulus
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

/-- Pure full-list weights BEFORE native sampling; no occurrence is deduplicated. -/
theorem constant_weight {A K : Type} [DecidableEq K] (items : List A) (key : A → K)
    (weight : A → F) (row : A) (same : ∀ a ∈ items, a = row) (one : weight row = 1) :
    weightAt items key weight (key row) = (items.length : F) := by
  induction items with
  | nil => simp [weightAt]
  | cons first rest ih =>
    have head := same first (by simp)
    have tail := ih (fun a member => same a (by simp [member]))
    subst first
    simpa [weightAt,one,Nat.cast_add,Nat.cast_one,add_comm] using congrArg (fun x : F => x+1) tail

theorem sampled_constant {A B : Type} (items : List A) (rows : A → Nat → B) (cap : Nat) (row : B)
    (same : ∀ a ∈ items, ∀ i, rows a i = row) :
    ∀ value ∈ items.flatMap (fun a => (List.range cap).map (rows a)), value = row := by
  intro value member
  obtain ⟨a,am,vm⟩ := List.mem_flatMap.mp member
  obtain ⟨i,_,equal⟩ := List.mem_map.mp vm
  exact equal.symm.trans (same a am i)

/-- Euclidean arithmetic for EVERY native allowed main count, including >=257.
    Capacity is 8388607 and the characteristic is 256*capacity+255. -/
theorem residue_not_bit {n bit : Nat} (positive : 0 < n) (bound : n ≤ 8192) (boolean : bit ≤ 1) :
    ((n*8388607 : Nat) : F) ≠ (bit : F) := by
  intro equal
  obtain ⟨q,qb,balance⟩ := (NativeCallerCountProofs.quotient (by omega) boolean equal).2
  change n*8388607 = bit+2147483647*q at balance
  have lower : 256*q ≤ n := by omega
  have upper : n ≤ 256*q := by omega
  have exactCount : n = 256*q := by omega
  omega

open Airbender.ReducedMachine.Native Airbender.ReducedMachine.NativeMemoryBoundary
open Airbender.Blake2Worker Airbender.Blake2Worker.Native Airbender.Trace

theorem copy_proofs {R : Type} [Field R] (proof : NativeMainDecoder.Proof R) (count : BitVec 32) :
    (copies proof count).main.proofs = List.replicate count.toNat proof.initialization := by
  simp [copies,NativeMainDecoder.Batch.main,NativeMainBatch.Batch.proofs]

theorem copy_rows {R : Type} [Field R] (proof : NativeMainDecoder.Proof R) (count : BitVec 32)
    (row : Nat → F) (same : proof.initialization.main.memory.rows = fun _ => row) :
    ∀ value ∈ callerRows (copies proof count).main.proofs, value = row := by
  change ∀ value ∈ (NativeInitializationBatch.mainProofs (copies proof count).main.proofs).flatMap
    (fun (p : Airbender.ReducedMachine.NativeMainAuxiliary.MainProof R) =>
      (List.range (callerAuxiliaryLayout.traceLength-1)).map p.rows), value = row
  apply sampled_constant _ (fun (p : Airbender.ReducedMachine.NativeMainAuxiliary.MainProof R) i => p.rows i) _ row
  intro p member i
  obtain ⟨source,sm,equal⟩ := List.mem_map.mp member
  have sourceSame : source = proof.initialization := by
    rw [copy_proofs] at sm
    exact (List.mem_replicate.mp sm).2
  subst source
  subst p
  exact congrFun same i

theorem copy_weight {R : Type} [Field R] (proof : NativeMainDecoder.Proof R) (count : BitVec 32)
    (row : Nat → F) (same : proof.initialization.main.memory.rows = fun _ => row) (one : row 92 = 1) :
    NativeDelegationKeyAccounting.callerWeight (copies proof count).main.proofs (callerKey row) =
      ((count.toNat*8388607 : Nat) : F) := by
  have all := copy_rows proof count row same
  have weight := constant_weight _ callerKey (fun w => w 92) row all one
  have length := NativeMainBatchProofs.ordinary_count (copies proof count).main
  rw [NativeMainBatchProofs.count_binding] at length
  change (callerRows (copies proof count).main.proofs).length = count.toNat*8388607 at length
  exact weight.trans (congrArg (fun n : Nat => (n : F)) length)

theorem inactive_lookups {Kind R : Type} [Field R] (publicSetup : SparseDecoderSetup Kind)
    (proof : NativeMainDecoder.Proof R) (count : BitVec 32) (row : Nat → F)
    (same : proof.initialization.main.memory.rows = fun _ => row)
    (inactive : row importedConstraintsTraceColumns.execute = 0) :
    NativeMainDecoder.LogicalLookups publicSetup (copies proof count) := by
  intro source member i ib active
  have sameSource : source = proof := by
    have mem : source ∈ List.replicate count.toNat proof := by
      simpa [NativeMainDecoder.Batch.proofs,copies] using member
    exact (List.mem_replicate.mp mem).2
  subst source
  rw [congrFun same i,inactive] at active
  exact (zero_ne_one active).elim

/-- Generic source rejection on these actual constant rows. Activity/count/
    matching are DERIVED through the old complete accepted relation. -/
theorem reject_constant {Setup R : Type} [Field R]
    (publicSetup : SparseDecoderSetup NativeCallerDecoder.Mode)
    (embed : F →+* R) (memory : MemoryKeyChallenges R) (ch : CSRArgumentChallenges R)
    (pc : PCChallenges R) (gamma : R)
    (decoder : Airbender.ReducedMachine.NativeDecoderArguments.Challenges R) (config : WorkerConfiguration Setup)
    (proof : NativeMainDecoder.Proof R) (countWord : BitVec 32) (row : Nat → F)
    (same : proof.initialization.main.memory.rows = fun _ => row)
    (inactive : row importedConstraintsTraceColumns.execute = 0) (one : row 92 = 1)
    {workers : WorkerBatch Setup R} {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    {before : Reference.RiscV.Sail.State} {count : Nat}
    (image : NativeCallerDecoder.setupImage before count 20 = some publicSetup)
    (accepted : NativeMainDecoder.SourceAccepted publicSetup embed memory ch pc gamma decoder config (copies proof countWord) workers inputs inverse)
    (identity : SourceIdentity (copies proof countWord).main.proofs workers) : False := by
  have limits := (NativeMainBatchProofs.counter_iff _).mp accepted.counted.counter
  change 0 < countWord.toNat ∧ countWord.toNat ≤ 8192 at limits
  have lookups := inactive_lookups publicSetup proof countWord row same inactive
  have prior := NativeDelegationKeyAccountingProofs.counted publicSetup embed memory ch pc gamma decoder config accepted image lookups identity
  have bit := prior.aggregateBoolean (callerKey row)
  rw [copy_weight proof countWord row same one] at bit
  rcases bit with zero | one
  · exact residue_not_bit limits.1 limits.2 (by decide : 0 ≤ 1) zero
  · exact residue_not_bit limits.1 limits.2 (by decide : 1 ≤ 1) one

theorem packed_main {R : Type} [Field R] (gamma : R)
    (proof : Airbender.ReducedMachine.NativeDecoderTableArguments.Proof R)
    (base : Nat → BaseAuxiliaryColumn → F) (witness : Nat → Scalar16WitnessColumn → F)
    (setup : Nat → Scalar16SetupColumn → F) (polynomial : Polynomial R) (omega : R) :
    (packed gamma proof base witness setup polynomial omega).initialization.main = proof.main := rfl

theorem packed_scalar {R : Type} [Field R] (gamma : R)
    (proof : Airbender.ReducedMachine.NativeDecoderTableArguments.Proof R)
    (base : Nat → BaseAuxiliaryColumn → F) (witness : Nat → Scalar16WitnessColumn → F)
    (setup : Nat → Scalar16SetupColumn → F) (polynomial : Polynomial R) (omega : R) :
    (packed gamma proof base witness setup polynomial omega).initialization.scalar =
      NativeScalarTableCompletion.scalarView gamma proof.main base witness setup polynomial omega := rfl

theorem packed_decoder {R : Type} [Field R] (gamma : R)
    (proof : Airbender.ReducedMachine.NativeDecoderTableArguments.Proof R)
    (base : Nat → BaseAuxiliaryColumn → F) (witness : Nat → Scalar16WitnessColumn → F)
    (setup : Nat → Scalar16SetupColumn → F) (polynomial : Polynomial R) (omega : R) :
    (packed gamma proof base witness setup polynomial omega).decoder = proof := rfl

theorem packed_values {R : Type} [Field R] (gamma : R)
    (proof : Airbender.ReducedMachine.NativeDecoderTableArguments.Proof R)
    (base : Nat → BaseAuxiliaryColumn → F) (witness : Nat → Scalar16WitnessColumn → F)
    (setup : Nat → Scalar16SetupColumn → F) (polynomial : Polynomial R) (omega : R) :
    (packed gamma proof base witness setup polynomial omega).initialization.values =
      NativeInitializationComponent.observedValues
        (NativeScalarTableCompletion.scalarView gamma proof.main base witness setup polynomial omega) := rfl

theorem original_fields :
    Airbender.ReducedMachine.NativeCSRPositiveWitness.assignment false importedConstraintsTraceColumns.execute = 0 ∧
    Airbender.ReducedMachine.NativeCSRPositiveWitness.assignment false 92 = 1 ∧
    callerKey (Airbender.ReducedMachine.NativeCSRPositiveWitness.assignment false) = ⟨1991,0,7,0⟩ := by
  decide +kernel

/-- The actual original complete component cannot extend to full source acceptance
    plus the OLD explicit source-identity boundary, for ANY u32-indexed copies and
    ANY complete worker batch. Not a physical-verifier or native-defect claim. -/
theorem reject_completion {Setup R : Type} [Field R]
    (publicSetup : SparseDecoderSetup NativeCallerDecoder.Mode)
    (embed : F →+* R) (memory : MemoryKeyChallenges R) (ch : CSRArgumentChallenges R)
    (pc : PCChallenges R) (gamma : R)
    (decoder : Airbender.ReducedMachine.NativeDecoderArguments.Challenges R) (config : WorkerConfiguration Setup)
    (beforeMain : Airbender.ReducedMachine.NativeMainAuxiliary.MainProof R) (omega : R)
    (proof : Airbender.ReducedMachine.NativeDecoderTableArguments.Proof R)
    (base : Nat → BaseAuxiliaryColumn → F) (witness : Nat → Scalar16WitnessColumn → F)
    (setup : Nat → Scalar16SetupColumn → F) (polynomial : Polynomial R)
    (completion : NativeInitializationComponent.Completion embed memory pc ch decoder gamma
      (Airbender.ReducedMachine.NativeCSRPositiveWitness.assignment false) beforeMain omega proof base witness setup polynomial)
    (countWord : BitVec 32) (workers : WorkerBatch Setup R) (inputs : PublicBoundary) (inverse : BoundaryInverses R)
    {before : Reference.RiscV.Sail.State} {count : Nat}
    (image : NativeCallerDecoder.setupImage before count 20 = some publicSetup) :
    ¬ (NativeMainDecoder.SourceAccepted publicSetup embed memory ch pc gamma decoder config
      (copies (packed gamma proof base witness setup polynomial omega) countWord) workers inputs inverse ∧
      SourceIdentity (copies (packed gamma proof base witness setup polynomial omega) countWord).main.proofs workers) := by
  rintro ⟨accepted,identity⟩
  apply reject_constant publicSetup embed memory ch pc gamma decoder config
    (packed gamma proof base witness setup polynomial omega) countWord
    (Airbender.ReducedMachine.NativeCSRPositiveWitness.assignment false) _
    original_fields.1 original_fields.2.1 image accepted identity
  change proof.main.memory.rows = _
  exact completion.source.paired.decoder.caller.components.1
end Airbender.NativeInactiveGlobalProofs
