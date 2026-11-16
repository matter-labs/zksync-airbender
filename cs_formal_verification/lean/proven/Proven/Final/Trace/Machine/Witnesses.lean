import Human.Trace.Machine.Padding
import Human.Trace.Machine.CodeWindows
import Human.ISA.Sail.MachineTargets
import Human.ISA.Sail.NativeTargets
import Proven.NonVacuous.NativeMachines
import Proven.NonVacuous.DynamicCopyLoop.Accepted
import Proven.NonVacuous.DynamicCopyLoop.Native
import Proven.NonVacuous.UnrolledNative.Certificates

namespace Airbender.NonVacuous.Machine
open Airbender Trace Trace.Machine Arithmetic Compiler NativeArithmetic PaddingBoundary
set_option warningAsError true

private theorem pooled_accepted : UnrolledAcceptance pooled workers [] := by
  refine ⟨workers_accepted, ?_, ?_, List.Perm.refl _, ?_, List.Perm.refl _, ?_⟩
  · intro row member; cases member
  · intro row member; cases member
  · intro row member; cases member
  · exact pooled_arguments.memory

private theorem unified_accepted : UnifiedAcceptance unifiedTrace workers [] := by
  refine ⟨workers_accepted, ?_, ?_, List.Perm.refl _, ?_, List.Perm.refl _, ?_⟩
  · intro row member; cases member
  · intro row member; cases member
  · intro row member; cases member
  · exact unified_arguments.memory

private theorem masked_workers : MaskedWorkersAccepted workers := by
  constructor <;> intro row member <;> cases member

private theorem pooled_masked : MaskedUnrolledAcceptance pooled workers [] := by
  refine ⟨masked_workers, ?_, ?_, ?_, List.Perm.refl _, List.Perm.refl _, ?_⟩
  · intro row member; cases member
  · intro row member; cases member
  · intro row member; cases member
  · have memory := pooled_memory
    simp only [maskedUnrolledTokens, maskedWorkerTokens, contributions,
      show pooled.rows = [] from rfl, show workers.standard.rows = [] from rfl,
      show workers.split.rows = [] from rfl, List.flatMap_nil, List.append_nil]
    exact memory.map some

private theorem unified_masked : MaskedUnifiedAcceptance unifiedTrace workers [] := by
  refine ⟨masked_workers, ?_, ?_, ?_, List.Perm.refl _, List.Perm.refl _, ?_⟩
  · intro row member; cases member
  · intro row member; cases member
  · intro row member; cases member
  · have memory := unified_memory
    simp only [maskedUnifiedTokens, maskedWorkerTokens, contributions,
      show unifiedTrace.rows = [] from rfl, show workers.standard.rows = [] from rfl,
      show workers.split.rows = [] from rfl, List.flatMap_nil, List.append_nil]
    exact memory.map some

private theorem pooled_initial_bounded : (timeOfPair pooled.initial.timestamp).Bounded := by
  change 4 < 524288 ∧ 0 < 524288
  decide +kernel

private theorem unified_initial_bounded : (timeOfPair unifiedTrace.initial.timestamp).Bounded := by
  change 4 < 524288 ∧ 0 < 524288
  decide +kernel

end Airbender.NonVacuous.Machine

namespace Airbender.Trace.Machine
open Airbender.NonVacuous.Machine
set_option warningAsError true

/-- Public unrolled boot data and acceptance meet the full target's premises. -/
theorem unrolled_full_unsigned_satisfiable : UnrolledFullUnsignedSatisfiableClaim := by
  refine ⟨pooled, workers, zero, cells InitsTeardowns.importedLayout standaloneInits, [], standaloneInits,
    ?_, rfl, rfl, rfl, ?_, ?_, pooled_accepted⟩
  · exact boot .unrolledFullUnsigned _ _ (InitsTeardowns.Proofs.claims ⟨rfl, Or.inr rfl⟩) _ standalone_checked
  · intro entry member; cases member
  · intro row member; cases member

/-- Public unrolled boot data and acceptance meet the reduced target's premises. -/
theorem unrolled_reduced_satisfiable : UnrolledReducedSatisfiableClaim := by
  refine ⟨pooled, workers, zero, cells InitsTeardowns.importedLayout standaloneInits, [], standaloneInits,
    ?_, rfl, rfl, rfl, ?_, pooled_accepted⟩
  · exact boot .unrolledReduced _ _ (InitsTeardowns.Proofs.claims ⟨rfl, Or.inr rfl⟩) _ standalone_checked
  · intro row member; cases member

/-- A loop with sixteen CPU rows and two bigint calls meets every unified target premise. -/
theorem unified_satisfiable : UnifiedSatisfiableClaim := NonVacuous.DynamicCopyLoop.witness

/-- A full masked unrolled layout meets every padded full target premise. -/
theorem padded_unrolled_full_unsigned_satisfiable : PaddedUnrolledFullUnsignedSatisfiableClaim := by
  refine ⟨pooled, workers, zero, cells InitsTeardowns.importedLayout standaloneInits, [], standaloneInits,
    ?_, rfl, rfl, rfl, ?_, ?_, pooled_masked⟩
  · exact boot .unrolledFullUnsigned _ _ (InitsTeardowns.Proofs.claims ⟨rfl, Or.inr rfl⟩) _ standalone_checked
  · intro entry member; cases member
  · intro row member; cases member

/-- A full masked unrolled layout meets every padded reduced target premise. -/
theorem padded_unrolled_reduced_satisfiable : PaddedUnrolledReducedSatisfiableClaim := by
  refine ⟨pooled, workers, zero, cells InitsTeardowns.importedLayout standaloneInits, [], standaloneInits,
    ?_, rfl, rfl, rfl, ?_, pooled_masked⟩
  · exact boot .unrolledReduced _ _ (InitsTeardowns.Proofs.claims ⟨rfl, Or.inr rfl⟩) _ standalone_checked
  · intro row member; cases member

/-- A full masked unified layout meets every padded unified target premise. -/
theorem padded_unified_satisfiable : PaddedUnifiedSatisfiableClaim := by
  refine ⟨unifiedTrace, workers, zero, cells InitsTeardowns.unifiedLayout unifiedInits, [], unifiedInits,
    ?_, rfl, rfl, ?_, ?_, unified_masked⟩
  · exact boot .unified _ _ (InitsTeardowns.Proofs.claims ⟨rfl, Or.inl rfl⟩) _ unified_checked
  · intro entry member; cases member
  · intro row member; cases member

/-- The full Sail target has its own simultaneous premise witness. -/
theorem unrolled_full_unsigned_sail_satisfiable : UnrolledFullUnsignedSailSatisfiableClaim :=
  unrolled_full_unsigned_satisfiable

/-- The reduced Sail target has its own simultaneous premise witness. -/
theorem unrolled_reduced_sail_satisfiable : UnrolledReducedSailSatisfiableClaim := unrolled_reduced_satisfiable

/-- The unified Sail target has its own simultaneous premise witness. -/
theorem unified_sail_satisfiable : UnifiedSailSatisfiableClaim := unified_satisfiable

/-- Empty hash windows meet all unrolled segmentation premises. -/
theorem unrolled_hash_segmentation_satisfiable : UnrolledHashSegmentationSatisfiableClaim := by
  refine ⟨pooled, workers, [], [], pooled_accepted, pooled_initial_bounded, by decide +kernel, ?_⟩
  constructor
  · exact List.Pairwise.nil
  · intro request member; cases member
  · intro window member; cases member
  · intro window member; cases member

/-- Empty hash windows meet all unified segmentation premises. -/
theorem unified_hash_segmentation_satisfiable : UnifiedHashSegmentationSatisfiableClaim := by
  refine ⟨unifiedTrace, workers, [], [], unified_accepted, unified_initial_bounded, by decide +kernel, ?_⟩
  constructor
  · exact List.Pairwise.nil
  · intro request member; cases member
  · intro window member; cases member
  · intro window member; cases member

/-- Public code, alignment and empty intervals meet all unrolled code-window premises. -/
theorem unrolled_code_hash_segmentation_satisfiable : UnrolledCodeHashSegmentationSatisfiableClaim := by
  refine ⟨.unrolledFullUnsigned, pooled, workers, zero, [], [], [], by decide +kernel, rfl,
    pooled_accepted, pooled_initial_bounded, by decide +kernel, List.Pairwise.nil, ?_, ?_⟩
  · intro request member; cases member
  · intro window member; cases member

/-- Public code, alignment and empty intervals meet all unified code-window premises. -/
theorem unified_code_hash_segmentation_satisfiable : UnifiedCodeHashSegmentationSatisfiableClaim := by
  refine ⟨unifiedTrace, workers, zero, [], [], [], rfl,
    unified_accepted, unified_initial_bounded, by decide +kernel, List.Pairwise.nil, ?_, ?_⟩
  · intro request member; cases member
  · intro window member; cases member

end Airbender.Trace.Machine

namespace Airbender.Trace.Machine.Native
open Airbender.Compiler Airbender.NonVacuous.Machine
set_option warningAsError true

/-- One active CPU row meets every full native Sail target premise. -/
theorem unrolled_full_from_native_sail_satisfiable : UnrolledFullFromNativeSailSatisfiableClaim := by
  obtain ⟨trace, workers, initial, cells, program, inits, tables, _, _, _, premises⟩ := full_native
  exact ⟨trace, workers, initial, cells, program, inits, tables, premises⟩

/-- One active CPU row meets every reduced native Sail target premise. -/
theorem unrolled_reduced_from_native_sail_satisfiable : UnrolledReducedFromNativeSailSatisfiableClaim := by
  obtain ⟨trace, workers, initial, cells, program, inits, tables, _, _, _, premises⟩ := reduced_native
  exact ⟨trace, workers, initial, cells, program, inits, tables, premises⟩

/-- Sixteen CPU rows and two bigint calls meet every unified native Sail target premise. -/
theorem unified_from_native_sail_satisfiable : UnifiedFromNativeSailSatisfiableClaim := by
  obtain ⟨trace, workers, initial, cells, program, inits, tables, _, _, _, premises⟩ := unified_native
  exact ⟨trace, workers, initial, cells, program, inits, tables, premises⟩

end Airbender.Trace.Machine.Native

namespace Airbender.PaddingBoundary
open Airbender.NonVacuous.Machine

/-- The accepted padded layout has the full projection boundary. -/
theorem projection_satisfiable : ProjectionSatisfiableClaim := by
  refine ⟨pooled, ?_, ?_⟩
  · intro row member; cases member
  · refine ⟨?_, List.Perm.refl _, ?_⟩
    · intro row member; cases member
    · have memory := pooled_memory
      change (pooled.initialMemory.map some ++ []).Perm (pooled.terminalMemory.map some ++ [])
      simpa only [List.append_nil] using memory.map some

end Airbender.PaddingBoundary
