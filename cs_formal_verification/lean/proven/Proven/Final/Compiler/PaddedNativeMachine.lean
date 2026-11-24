module
public import Proven.Trace.Machine.PaddedNative
public import Proven.Final.Compiler.NativeMachine
public import Proven.NonVacuous.PaddedNative.Unrolled
public import Proven.NonVacuous.PaddedNative.Unified

@[expose] public section
namespace Airbender.Trace.Machine.Native
open Airbender.Compiler PaddingBoundary Airbender.Trace.Machine.Proofs
set_option warningAsError true

/-- The active rows of a padded native layout execute the full unsigned whole-machine run. -/
theorem padded_unrolled_full_from_native : PaddedUnrolledFullFromNative := by
  intro trace workers initial cells program inits tables boot noSpecial stream bound covers certificates arguments
  exact unrolled_full_from_native (active trace) (activeWorkers workers) initial cells program inits tables
    boot noSpecial stream bound covers (activeCertificates certificates)
    (padded_unrolled_arguments arguments)

/-- The active rows of a padded native layout execute the reduced whole-machine run. -/
theorem padded_unrolled_reduced_from_native : PaddedUnrolledReducedFromNative := by
  intro trace workers initial cells program inits tables boot stream bound covers certificates arguments
  exact unrolled_reduced_from_native (active trace) (activeWorkers workers) initial cells program inits tables
    boot stream bound covers (activeCertificates certificates)
    (padded_unrolled_arguments arguments)

/-- The active rows of a padded native layout execute the unified whole-machine run. -/
theorem padded_unified_from_native : PaddedUnifiedFromNative := by
  intro trace workers initial cells program inits tables boot noSpecial stream bound certificates arguments
  exact unified_from_native (active trace) (activeWorkers workers) initial cells program inits tables
    boot noSpecial stream bound (activeUnifiedCertificates certificates)
    (padded_unified_arguments arguments)

/-- One active ADD row and one padding row meet the padded full unsigned native premises. -/
theorem padded_unrolled_full_from_native_satisfiable : PaddedUnrolledFullFromNativeSatisfiableClaim :=
  NonVacuous.PaddedNative.full_witness

/-- One active ADD row and one padding row meet the padded reduced native premises. -/
theorem padded_unrolled_reduced_from_native_satisfiable : PaddedUnrolledReducedFromNativeSatisfiableClaim :=
  NonVacuous.PaddedNative.reduced_witness

/-- One active unified ADD row and one padding row meet the padded unified native premises. -/
theorem padded_unified_from_native_satisfiable : PaddedUnifiedFromNativeSatisfiableClaim :=
  NonVacuous.PaddedNative.unified_witness

end Airbender.Trace.Machine.Native
