import Airbender.Review.Circuits.ReducedMachine.CallerDecoder
import Airbender.Proofs.ReducedMachine.NativeMainDecoder
import Airbender.Proofs.ReducedMachine.NativeCallerRequests
import Airbender.Proofs.ReducedMachine.NativeUnifiedDecoder
import Airbender.Proofs.ReducedMachine.NativeCSRDecoder
import Airbender.Proofs.ReducedMachine.NativeRuntimeCSRResult

namespace Airbender.NativeCallerDecoderProofs
open Airbender.NativeCallerDecoder
open Airbender.ReducedMachine.Native Airbender.Trace Airbender.Verification
open Airbender.ReducedMachine.NativeMemoryBoundary Airbender.Blake2Worker.Native
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

/-- Entire finite mask calculations before any witness/native table instance. -/
theorem shift_bit (mode : ShiftMode) (useRegister : Bool) :
    ((mode.mask useRegister : F).val / 128 % 2) = 0 := by
  cases mode <;> cases useRegister <;> decide +kernel

theorem arithmetic_bit (mode : ArithmeticMode) : ((mode.mask : F).val / 128 % 2) = 0 := by
  cases mode <;> decide +kernel

private theorem bitwise_mask_bit (useRegister : Bool) : ((bitwiseMask useRegister : F).val / 128 % 2) = 0 := by
  cases useRegister <;> decide +kernel

theorem bitwise_bit (mode : BitwiseMode) : ((mode.mask : F).val / 128 % 2) = 0 :=
  bitwise_mask_bit mode.useRegister

private theorem comparison_mask_bit (useRegister : Bool) : ((comparisonMask useRegister : F).val / 128 % 2) = 0 := by
  cases useRegister <;> decide +kernel

theorem comparison_bit (mode : ComparisonMode) : ((mode.mask : F).val / 128 % 2) = 0 :=
  comparison_mask_bit mode.useRegister

theorem branch_bit : ((branchMask : F).val / 128 % 2) = 0 := by decide +kernel

theorem jump_bit (mode : JumpMode) : ((jumpMask mode : F).val / 128 % 2) = 0 := by
  cases mode <;> decide +kernel

theorem memory_bit (mode : WordMemoryMode) : ((wordMemoryMask mode : F).val / 128 % 2) = 0 := by
  cases mode <;> decide +kernel

/-- Zero-bit consequence of complete BODY, not execute=0 or an auxiliary filter. -/
theorem disabled {w : Nat → F} (holds : FlatOperation.ConstraintsHoldFlat (environment w)
    (importedConstraints Airbender.ReducedMachine.NativeRuntimePool.table)) {mask : Nat}
    (same : w 12 = (mask : F)) (bit : ((mask : F).val / 128 % 2) = 0) :
    csrRequest w = ⟨0,0,some 0,3⟩ := by
  apply (Airbender.NativeCallerRequestProofs.body holds).disabled
  change (w 12).val / 128 % 2 = 0
  rw [same]
  exact bit

theorem supported_disabled {w : Nat → F} {entry : SupportedProgramEntry}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints Airbender.ReducedMachine.NativeRuntimePool.table))
    (fields : supportedDecoderFields entry.instruction = some entry.data) (query : decoderQuery w = entry.query) :
    csrRequest w = ⟨0,0,some 0,3⟩ := by
  rcases Airbender.ReducedMachine.NativeSupportedDecoderProofs.entry_profile fields with shift | arithmetic | bitwise | comparison | branch | jump
  · obtain ⟨selected,_,_,_,source,same⟩ := shift
    obtain ⟨useRegister,mask⟩ := (Airbender.ReducedMachine.NativeShiftDecoderProofs.decoded_fields source (query.trans same.symm)).mask
    exact disabled holds mask (shift_bit selected.data.family useRegister)
  · obtain ⟨selected,_,_,_,source,same⟩ := arithmetic
    exact disabled holds (Airbender.ReducedMachine.NativeArithmeticDecoderProofs.decoded_fields source (query.trans same.symm)).mask
      (arithmetic_bit selected.data.family)
  · obtain ⟨selected,_,_,_,source,same⟩ := bitwise
    exact disabled holds (Airbender.ReducedMachine.NativeBitwiseDecoderProofs.decoded_fields source (query.trans same.symm)).mask
      (bitwise_bit selected.data.family)
  · obtain ⟨selected,_,_,_,source,same⟩ := comparison
    exact disabled holds (Airbender.ReducedMachine.NativeComparisonDecoderProofs.decoded_fields source (query.trans same.symm)).mask
      (comparison_bit selected.data.family)
  · obtain ⟨selected,_,_,_,source,same⟩ := branch
    exact disabled holds (Airbender.ReducedMachine.NativeBranchDecoderProofs.decoded_fields source (query.trans same.symm)).mask branch_bit
  · obtain ⟨selected,_,_,_,source,same⟩ := jump
    exact disabled holds (Airbender.ReducedMachine.NativeJumpDecoderProofs.decoded_fields source (query.trans same.symm)).mask
      (jump_bit selected.data.family)

theorem unified_disabled {w : Nat → F} {entry : UnifiedProgramEntry}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints Airbender.ReducedMachine.NativeRuntimePool.table))
    (fields : unifiedDecoderFields entry.instruction = some entry.data) (query : decoderQuery w = entry.query) :
    csrRequest w = ⟨0,0,some 0,3⟩ := by
  rcases Airbender.ReducedMachine.NativeUnifiedDecoderProofs.entry_profile fields with ordinary | memory
  · obtain ⟨selected,_,_,_,source,_,same⟩ := ordinary
    exact supported_disabled holds source (query.trans same.symm)
  · obtain ⟨selected,_,_,_,source,_,same⟩ := memory
    exact disabled holds (Airbender.ReducedMachine.NativeWordMemoryDecoderProofs.decoded_fields source (query.trans same.symm)).mask
      (memory_bit selected.data.family)

/-- Copy of the unchanged sum-projection decomposition, preserving every field. -/
theorem entry_profile {entry : Program} (fields : Airbender.NativeCallerDecoder.decoderFields entry.instruction = some entry.data) :
    (∃ selected : UnifiedProgramEntry, selected.instruction = entry.instruction ∧
      unifiedDecoderFields selected.instruction = some selected.data ∧
      selected.query (p := mersenne31Modulus) = entry.query) ∨
    (∃ selected : CSRProgramEntry, selected.instruction = entry.instruction ∧
      csrDecoderFields selected.instruction = some selected.data ∧
      selected.query (p := mersenne31Modulus) = entry.query) := by
  unfold Airbender.NativeCallerDecoder.decoderFields at fields
  cases ordinary : unifiedDecoderFields entry.instruction with
  | some data =>
    simp only [ordinary] at fields
    have same := Option.some.inj fields
    refine Or.inl ⟨⟨entry.pc,entry.bits,entry.instruction,data⟩,rfl,ordinary,?_⟩
    unfold ProgramEntry.query
    rw [← same]
    rfl
  | none =>
    simp only [ordinary] at fields
    cases csr : csrDecoderFields entry.instruction with
    | none => simp [csr] at fields
    | some data =>
      simp only [csr,Option.map_some] at fields
      have same := Option.some.inj fields
      refine Or.inr ⟨⟨entry.pc,entry.bits,entry.instruction,data⟩,rfl,csr,?_⟩
      unfold ProgramEntry.query
      rw [← same]
      rfl

/-- Full CSR mask is derived from original public fields, not the selector alone. -/
theorem csr_shape {w : Nat → F} {entry : CSRProgramEntry}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints Airbender.ReducedMachine.NativeRuntimePool.table))
    (fields : csrDecoderFields entry.instruction = some entry.data) (query : decoderQuery w = entry.query) :
    (csrRequest w).multiplicity = 0 ∨ (csrRequest w).multiplicity = 1 := by
  have mask := (Airbender.ReducedMachine.NativeCSRDecoderProofs.decoded_fields fields query).mask
  have actual := Airbender.ReducedMachine.NativeRuntimeCSRResultProofs.effects holds mask
  rcases actual.key with nondeterminism | delegation
  · left
    rw [actual.request]
    simp only [nondeterminism,Airbender.ReducedMachine.NativeRuntimeCSR.delegated]
    decide +kernel
  · right
    rw [actual.request]
    simp only [delegation,Airbender.ReducedMachine.NativeRuntimeCSR.delegated]
    decide +kernel

theorem row {w : Nat → F} {entry : Program}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints Airbender.ReducedMachine.NativeRuntimePool.table))
    (fields : Airbender.NativeCallerDecoder.decoderFields entry.instruction = some entry.data) (query : decoderQuery w = entry.query) : RowEffects w entry := by
  rcases entry_profile fields with ordinary | csr
  · obtain ⟨selected,_,source,same⟩ := ordinary
    have zero := unified_disabled holds source (query.trans same.symm)
    exact ⟨Or.inl (congrArg CSRRequest.multiplicity zero),Or.inl zero⟩
  · obtain ⟨selected,instruction,source,same⟩ := csr
    have csrQuery := query.trans same.symm
    have mask := (Airbender.ReducedMachine.NativeCSRDecoderProofs.decoded_fields source csrQuery).mask
    have actual := Airbender.ReducedMachine.NativeRuntimeCSRResultProofs.effects holds mask
    refine ⟨csr_shape holds source csrQuery,?_⟩
    rcases actual.key with nondeterminism | delegation
    · left
      rw [actual.request,nondeterminism]
      simp [Airbender.ReducedMachine.NativeRuntimeCSR.delegated]
    · right
      obtain ⟨index,rs1,rd,original,data⟩ := Airbender.ReducedMachine.NativeCSRDecoderProofs.original_fields source
      have immediate := (Airbender.ReducedMachine.NativeCSRDecoderProofs.decoded_fields source csrQuery).immediate
      have key := congrArg (fun v : Vector F 2 => v[0]) immediate
      rw [data] at key
      change w 9 = (index.toNat : F) at key
      have keyVal : (w 9).val = index.toNat := by
        rw [key,ZMod.val_natCast_of_lt (lt_trans index.isLt (by decide))]
      have indexSame : index = (1991 : BitVec 12) := by
        apply BitVec.eq_of_toNat_eq
        exact keyVal.symm.trans delegation
      have requested : csrRequest w = ⟨1,1991,some (w 36),3⟩ := by
        rw [actual.request]
        have delegate : Airbender.ReducedMachine.NativeRuntimeCSR.delegated (w 9).val = 1 := by simp [Airbender.ReducedMachine.NativeRuntimeCSR.delegated,delegation]
        rw [delegate]
        have keyField : w 9 = (1991 : F) := by
          apply ZMod.val_injective
          exact delegation
        simp [keyField]
      refine ⟨rs1,rd,?_,mask,delegation,requested,actual.delegationZero (by simp [Airbender.ReducedMachine.NativeRuntimeCSR.delegated,delegation]),actual.offsetBounded⟩
      rw [← instruction,original,indexSame]

theorem effects {Setup R : Type} [Field R]
    (publicSetup : SparseDecoderSetup Mode) (embed : F →+* R) (memory : MemoryKeyChallenges R)
    (ch : CSRArgumentChallenges R) (pc : PCChallenges R) (gamma : R)
    (decoder : Airbender.ReducedMachine.NativeDecoderArguments.Challenges R) (config : WorkerConfiguration Setup)
    {batch : Airbender.NativeMainDecoder.Batch R} {workers : WorkerBatch Setup R} {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : Airbender.NativeMainDecoder.SourceAccepted publicSetup embed memory ch pc gamma decoder config batch workers inputs inverse)
    {before : Reference.RiscV.Sail.State} {count : Nat}
    (image : setupImage before count 20 = some publicSetup)
    (lookups : Airbender.NativeMainDecoder.LogicalLookups publicSetup batch) : Effects before publicSetup batch := by
  have sources := Airbender.NativeMainDecoderProofs.public_sources publicSetup embed memory ch pc gamma decoder config accepted image lookups
  intro proof member i ordinary active
  obtain ⟨entry,present,source,query⟩ := sources proof member i ordinary active
  exact ⟨entry,present,source,query,row (accepted.access proof member i ordinary).body source.fields query⟩

theorem joint {Setup R : Type} [Field R]
    (publicSetup : SparseDecoderSetup Mode) (embed : F →+* R) (memory : MemoryKeyChallenges R)
    (ch : CSRArgumentChallenges R) (pc : PCChallenges R) (gamma : R)
    (decoder : Airbender.ReducedMachine.NativeDecoderArguments.Challenges R) (config : WorkerConfiguration Setup)
    {batch : Airbender.NativeMainDecoder.Batch R} {workers : WorkerBatch Setup R} {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : Airbender.NativeMainDecoder.SourceAccepted publicSetup embed memory ch pc gamma decoder config batch workers inputs inverse)
    {before : Reference.RiscV.Sail.State} {count : Nat}
    (image : setupImage before count 20 = some publicSetup)
    (lookups : Airbender.NativeMainDecoder.LogicalLookups publicSetup batch) :
    Airbender.NativeMainBatch.Effects batch.main ∧
      Airbender.NativeMainDecoder.DecoderEffects publicSetup embed decoder batch ∧
      Airbender.NativeWorkerClockProgress.Effects workers ∧ Effects before publicSetup batch := by
  have previous := Airbender.NativeMainDecoderProofs.joint publicSetup embed memory ch pc gamma decoder config accepted
  exact ⟨previous.1,previous.2.1,previous.2.2,effects publicSetup embed memory ch pc gamma decoder config accepted image lookups⟩
end Airbender.NativeCallerDecoderProofs
