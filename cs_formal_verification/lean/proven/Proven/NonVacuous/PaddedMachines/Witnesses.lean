module
public import Proven.NonVacuous.PaddedMachines.Model

@[expose] public section
namespace Airbender.NonVacuous.PaddedMachines
open Trace Trace.Machine Arithmetic PaddingBoundary
set_option warningAsError true

/-- One active ADD row and one checked padding row meet the full unsigned target's premises. -/
theorem full_witness : PaddedUnrolledFullUnsignedSatisfiableClaim := by
  refine ⟨pooled, Machine.workers, PooledBoot.initial, PooledBoot.cells, UnrolledNative.program, PooledBoot.inits,
    ?_, rfl, rfl, rfl, UnrolledNative.no_special, ?_, pooled_masked,
    pooled_sizes.1, pooled_sizes.2.1, pooled_sizes.2.2.1, pooled_sizes.2.2.2⟩
  · simpa only [pooled_active] using UnrolledNative.boot .unrolledFullUnsigned (Or.inl rfl)
  · simpa only [pooled_active] using UnrolledNative.stream_ports

/-- The same complete masked ADD layout meets the reduced target's premises. -/
theorem reduced_witness : PaddedUnrolledReducedSatisfiableClaim := by
  refine ⟨pooled, Machine.workers, PooledBoot.initial, PooledBoot.cells, UnrolledNative.program, PooledBoot.inits,
    ?_, rfl, rfl, rfl, ?_, pooled_masked,
    pooled_sizes.1, pooled_sizes.2.1, pooled_sizes.2.2.1, pooled_sizes.2.2.2⟩
  · simpa only [pooled_active] using UnrolledNative.boot .unrolledReduced (Or.inr rfl)
  · simpa only [pooled_active] using UnrolledNative.stream_ports

/-- One active unified ADD row and one checked padding row meet every padded unified premise. -/
theorem unified_witness : PaddedUnifiedSatisfiableClaim := by
  refine ⟨unified, Machine.workers, UnifiedBoot.initial, UnifiedBoot.cells, unifiedProgram, UnifiedBoot.inits,
    ?_, rfl, rfl, unified_no_special, ?_, unified_masked,
    unified_sizes.1, unified_sizes.2.1, unified_sizes.2.2.1, unified_sizes.2.2.2⟩
  · simpa only [unified_active] using unified_boot
  · simpa only [unified_active] using unified_stream_ports

/-- Two constrained rows, with one selected row and one padding row, meet the projection boundary. -/
theorem projection_witness : ProjectionSatisfiableClaim :=
  ⟨pooled, pooled_layout, pooled_sizes.1, pooled_sizes.2.1, pooled_sizes.2.2.1, pooled_sizes.2.2.2⟩

end Airbender.NonVacuous.PaddedMachines
