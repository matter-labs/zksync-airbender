module
public import Proven.Compiler.CPUWitnesses.Unified.Padding
public import Proven.Compiler.NativeSatisfiable.Unified
public import Proven.NonVacuous.PaddedMachines.Model

@[expose] public section
namespace Airbender.NonVacuous.PaddedNative
open Trace Trace.Machine Compiler PaddingBoundary NonVacuous.PaddedMachines
set_option warningAsError true
set_option maxRecDepth 32768

/-- The public setup rows of the one-instruction unified program. -/
noncomputable def unifiedTables : ProgramLookupRows := NativePublicSetup.rows UnifiedBoot.initial unifiedProgram

/-- Every native tuple of the active unified row is a public table row. -/
theorem unified_lookup_check : CPUWitnesses.Unified.canonicalCheck UnifiedBoot.initial unifiedProgram
    UnifiedBoot.assignment = true := by
  kernel_rfl

/-- The active unified row has native gates, placement, public lookups and participation. -/
noncomputable def unifiedRowCertificate : UnifiedLogicalRowCertificate unifiedTables :=
  CPUWitnesses.Unified.of_checked UnifiedBoot.initial unifiedProgram UnifiedBoot.assignment
    NativeSatisfiable.Unified.source_satisfied unified_lookup_check (by kernel_rfl)

/-- The unified padding assignment satisfies every native source equation. -/
theorem unified_padding_source_check : FullArithmeticNative.UnifiedCached.native.artifact.source.all
    (fun polynomial => decide (evaluate (NativeExtension.Unified.inputValues unifiedPaddingAssignment) polynomial = 0)) =
      true := by
  kernel_rfl

theorem unified_padding_source_satisfied : Satisfies FullArithmeticNative.UnifiedCached.native.artifact.source
    (NativeExtension.Unified.inputValues unifiedPaddingAssignment) := by
  intro polynomial member
  exact of_decide_eq_true (List.all_eq_true.mp unified_padding_source_check polynomial member)

/-- Every enabled tuple of the unified padding row is a public table row. -/
theorem unified_padding_lookup_check : CPUWitnesses.canonicalCheck .unified UnifiedBoot.initial unifiedProgram
    (CPUWitnesses.Unified.paddingTuples unifiedPaddingAssignment) = true := by
  kernel_rfl

/-- The unified padding row has native gates, placement and public lookups with execute zero. -/
noncomputable def unifiedPaddingCertificate : UnifiedRowCertificate unifiedTables :=
  CPUWitnesses.Unified.padding_of_checked UnifiedBoot.initial unifiedProgram unifiedPaddingAssignment
    unified_padding_source_satisfied unified_padding_lookup_check rfl

noncomputable def unifiedCertificates : List (UnifiedRowCertificate unifiedTables) :=
  [unifiedPaddingCertificate, unifiedRowCertificate.toUnifiedRowCertificate]

/-- The unified ADD metadata fits the native decoder and has zero omitted coordinates. -/
theorem unified_tables_bound : NativePublicSetup.Bound UnifiedBoot.initial unifiedProgram unifiedTables := by
  constructor
  · rfl
  · decide +kernel
  · intro candidate member
    obtain rfl := List.mem_singleton.mp member
    left
    decide +kernel
  · intro candidate member index omitted
    obtain rfl := List.mem_singleton.mp member
    have checked : ∀ index : Fin 9,
        (NativeLookups.circuitFor unifiedEntry.data.family).decode_table_columns_mask[index.val]?.getD false = false →
          (unifiedEntry.data.row unifiedEntry.pc)[index] = 0 := by decide +kernel
    exact checked index omitted

theorem unified_arguments : PaddedUnifiedNativeArguments unifiedTables unifiedCertificates unified Machine.workers := by
  refine ⟨⟨[], by simp, rfl, rfl⟩, rfl, ?_, unified_masked.states, unified_masked.requests,
    unified_masked.memory⟩
  intro entry member
  simp only [unifiedCertificates, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr unifiedRowCertificate.active

/-- One active unified ADD row and one padding row meet the padded unified native premises. -/
theorem unified_witness : Native.PaddedUnifiedFromNativeSatisfiableClaim := by
  refine ⟨unified, Machine.workers, UnifiedBoot.initial, UnifiedBoot.cells, unifiedProgram, UnifiedBoot.inits,
    unifiedTables, unified_sizes.2.2.1, unified_sizes.2.2.2, ?_, unified_no_special, ?_,
    unified_tables_bound, unifiedCertificates, unified_arguments⟩
  · simpa only [unified_active] using unified_boot
  · simpa only [unified_active] using unified_stream_ports

end Airbender.NonVacuous.PaddedNative
