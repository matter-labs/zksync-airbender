import Human.Trace.Machine.Padding
import Human.Trace.Machine.CodeWindows
import Human.ISA.Sail.MachineTargets
import Human.ISA.Sail.NativeTargets
import Proven.NonVacuous.NativeMachines
import Proven.NonVacuous.DynamicCopyLoop.Accepted
import Proven.NonVacuous.DynamicCopyLoop.Native
import Proven.NonVacuous.UnrolledNative.Certificates
import Proven.NonVacuous.PaddedMachines.Witnesses
import Proven.NonVacuous.RoundWindow.Acceptance

namespace Airbender.Trace.Machine
open Airbender.NonVacuous.Machine
set_option warningAsError true

/-- One active ADD row meets every full unrolled target premise. -/
theorem unrolled_full_unsigned_satisfiable : UnrolledFullUnsignedSatisfiableClaim := by
  refine ⟨NonVacuous.UnrolledNative.trace, workers, NonVacuous.PooledBoot.initial, NonVacuous.PooledBoot.cells,
    NonVacuous.UnrolledNative.program, NonVacuous.PooledBoot.inits,
    List.cons_ne_nil _ _, rfl, NonVacuous.UnrolledNative.boot _ (Or.inl rfl), rfl, rfl, rfl,
    NonVacuous.UnrolledNative.no_special, NonVacuous.UnrolledNative.stream_ports,
    NonVacuous.PaddedMachines.pooled_accepted⟩

/-- One active ADD row meets every reduced unrolled target premise. -/
theorem unrolled_reduced_satisfiable : UnrolledReducedSatisfiableClaim := by
  refine ⟨NonVacuous.UnrolledNative.trace, workers, NonVacuous.PooledBoot.initial, NonVacuous.PooledBoot.cells,
    NonVacuous.UnrolledNative.program, NonVacuous.PooledBoot.inits,
    List.cons_ne_nil _ _, rfl, NonVacuous.UnrolledNative.boot _ (Or.inr rfl), rfl, rfl, rfl,
    NonVacuous.UnrolledNative.stream_ports, NonVacuous.PaddedMachines.pooled_accepted⟩

/-- A loop with sixteen CPU rows and two bigint calls meets every unified target premise. -/
theorem unified_satisfiable : UnifiedSatisfiableClaim := NonVacuous.DynamicCopyLoop.witness

/-- One active ADD row and one constrained padding row meet every padded full premise. -/
theorem padded_unrolled_full_unsigned_satisfiable : PaddedUnrolledFullUnsignedSatisfiableClaim :=
  NonVacuous.PaddedMachines.full_witness

/-- One active ADD row and one constrained padding row meet every padded reduced premise. -/
theorem padded_unrolled_reduced_satisfiable : PaddedUnrolledReducedSatisfiableClaim :=
  NonVacuous.PaddedMachines.reduced_witness

/-- One active unified ADD row and one constrained padding row meet every padded unified premise. -/
theorem padded_unified_satisfiable : PaddedUnifiedSatisfiableClaim := NonVacuous.PaddedMachines.unified_witness

/-- One active ADD row meets every full unrolled Sail premise. -/
theorem unrolled_full_unsigned_sail_satisfiable : UnrolledFullUnsignedSailSatisfiableClaim :=
  unrolled_full_unsigned_satisfiable

/-- One active ADD row meets every reduced unrolled Sail premise. -/
theorem unrolled_reduced_sail_satisfiable : UnrolledReducedSailSatisfiableClaim := unrolled_reduced_satisfiable

/-- The unified Sail target has its own simultaneous premise witness. -/
theorem unified_sail_satisfiable : UnifiedSailSatisfiableClaim := unified_satisfiable

/-- Ten matched round calls supply one complete unrolled hash window. -/
theorem unrolled_hash_segmentation_satisfiable : UnrolledHashSegmentationSatisfiableClaim :=
  ⟨NonVacuous.RoundWindow.unrolledTrace, NonVacuous.RoundWindow.workers,
    NonVacuous.RoundWindow.unrolledProgram, NonVacuous.RoundWindow.windows,
    NonVacuous.RoundWindow.unrolled_rows_nonempty, NonVacuous.RoundWindow.unrolled_rows_length,
    NonVacuous.RoundWindow.worker_rows_length, NonVacuous.RoundWindow.split_rows,
    List.cons_ne_nil _ _, NonVacuous.RoundWindow.windows_length,
    NonVacuous.RoundWindow.unrolled_accepted, NonVacuous.RoundWindow.unrolled_initial_bounded,
    NonVacuous.RoundWindow.unrolled_initial_aligned, NonVacuous.RoundWindow.unrolled_profile⟩

/-- Ten matched round calls supply one complete unified hash window. -/
theorem unified_hash_segmentation_satisfiable : UnifiedHashSegmentationSatisfiableClaim :=
  ⟨NonVacuous.RoundWindow.unifiedTrace, NonVacuous.RoundWindow.workers,
    NonVacuous.RoundWindow.unifiedProgram, NonVacuous.RoundWindow.windows,
    NonVacuous.RoundWindow.unified_rows_nonempty, NonVacuous.RoundWindow.unified_rows_length,
    NonVacuous.RoundWindow.worker_rows_length, NonVacuous.RoundWindow.split_rows,
    List.cons_ne_nil _ _, NonVacuous.RoundWindow.windows_length,
    NonVacuous.RoundWindow.unified_accepted, NonVacuous.RoundWindow.unified_initial_bounded,
    NonVacuous.RoundWindow.unified_initial_aligned, NonVacuous.RoundWindow.unified_profile⟩

/-- Public round code and the complete interval meet every unrolled code-window premise. -/
theorem unrolled_code_hash_segmentation_satisfiable : UnrolledCodeHashSegmentationSatisfiableClaim :=
  ⟨.unrolledFullUnsigned, NonVacuous.RoundWindow.unrolledTrace, NonVacuous.RoundWindow.workers,
    NonVacuous.RoundWindow.initial, NonVacuous.RoundWindow.addresses,
    NonVacuous.RoundWindow.unrolledProgram, NonVacuous.RoundWindow.windows,
    NonVacuous.RoundWindow.unrolled_rows_nonempty, NonVacuous.RoundWindow.unrolled_rows_length,
    NonVacuous.RoundWindow.worker_rows_length, NonVacuous.RoundWindow.split_rows,
    List.cons_ne_nil _ _, NonVacuous.RoundWindow.windows_length, by decide +kernel,
    NonVacuous.RoundWindow.unrolled_program_image, NonVacuous.RoundWindow.unrolled_accepted,
    NonVacuous.RoundWindow.unrolled_initial_bounded, NonVacuous.RoundWindow.unrolled_initial_aligned,
    NonVacuous.RoundWindow.unrolled_profile.separated, NonVacuous.RoundWindow.unrolled_profile.coverage,
    NonVacuous.RoundWindow.unrolled_scope⟩

/-- Public round code and the complete interval meet every unified code-window premise. -/
theorem unified_code_hash_segmentation_satisfiable : UnifiedCodeHashSegmentationSatisfiableClaim :=
  ⟨NonVacuous.RoundWindow.unifiedTrace, NonVacuous.RoundWindow.workers,
    NonVacuous.RoundWindow.initial, NonVacuous.RoundWindow.addresses,
    NonVacuous.RoundWindow.unifiedProgram, NonVacuous.RoundWindow.windows,
    NonVacuous.RoundWindow.unified_rows_nonempty, NonVacuous.RoundWindow.unified_rows_length,
    NonVacuous.RoundWindow.worker_rows_length, NonVacuous.RoundWindow.split_rows,
    List.cons_ne_nil _ _, NonVacuous.RoundWindow.windows_length,
    NonVacuous.RoundWindow.unified_program_image, NonVacuous.RoundWindow.unified_accepted,
    NonVacuous.RoundWindow.unified_initial_bounded, NonVacuous.RoundWindow.unified_initial_aligned,
    NonVacuous.RoundWindow.unified_profile.separated, NonVacuous.RoundWindow.unified_profile.coverage,
    NonVacuous.RoundWindow.unified_scope⟩

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

/-- One participating ADD row and one constrained padding row meet the complete projection boundary. -/
theorem projection_satisfiable : ProjectionSatisfiableClaim := NonVacuous.PaddedMachines.projection_witness

end Airbender.PaddingBoundary
