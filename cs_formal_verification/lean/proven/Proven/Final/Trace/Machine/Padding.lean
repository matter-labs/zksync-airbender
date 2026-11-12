module
public import Proven.Trace.Machine.PaddingProjection
public import Proven.Final.Trace.Machine.Unrolled
public import Proven.Final.Trace.Machine.Unified

@[expose] public section
namespace Airbender.Trace.Machine
open Airbender.Trace.Machine.Proofs PaddingBoundary
set_option warningAsError true

/-- The full masked unsigned layout executes through its active CPU and worker projection. -/
theorem padded_unrolled_full_unsigned : PaddedUnrolledFullUnsigned := by
  intro trace workers initial cells program inits boot wordSetup subwordSetup tables noSpecial noMop stream accepted
  exact unrolled_full_unsigned (active trace) (activeWorkers workers) initial cells program inits
    boot wordSetup subwordSetup tables noSpecial noMop stream (masked_unrolled_acceptance accepted)

/-- The full masked reduced layout executes with modular operations and round calls. -/
theorem padded_unrolled_reduced : PaddedUnrolledReduced := by
  intro trace workers initial cells program inits boot wordSetup subwordSetup tables stream accepted
  exact unrolled_reduced (active trace) (activeWorkers workers) initial cells program inits
    boot wordSetup subwordSetup tables stream (masked_unrolled_acceptance accepted)

/-- The full masked unified layout executes through its active CPU and worker projection. -/
theorem padded_unified : PaddedUnified := by
  intro trace workers initial cells program inits boot setup tables noSpecial stream accepted
  exact unified (active trace) (activeWorkers workers) initial cells program inits
    boot setup tables noSpecial stream (masked_unified_acceptance accepted)

end Airbender.Trace.Machine
