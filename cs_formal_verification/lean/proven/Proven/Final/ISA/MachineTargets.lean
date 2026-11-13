import Human.ISA.Sail.MachineTargets
import Proven.ISA.Equiv.WholeRun
import Proven.Final.Trace.Machine.Unrolled
import Proven.Final.Trace.Machine.Unified

namespace Airbender.Trace.Machine

/-- Every accepted full unsigned execution has a configured Airbender machine execution. -/
theorem unrolled_full_unsigned_sail : UnrolledFullUnsignedSailClaim := by
  intro trace workers initial cells program inits boot wordSetup subwordSetup tables noSpecial noMop stream accepted
  exact Proven.Equiv.sail_realizes
    (unrolled_full_unsigned trace workers initial cells program inits boot wordSetup subwordSetup tables
      noSpecial noMop stream accepted)

/-- Every accepted reduced execution has a configured Airbender machine execution. -/
theorem unrolled_reduced_sail : UnrolledReducedSailClaim := by
  intro trace workers initial cells program inits boot wordSetup subwordSetup tables stream accepted
  exact Proven.Equiv.sail_realizes
    (unrolled_reduced trace workers initial cells program inits boot wordSetup subwordSetup tables stream accepted)

/-- Every accepted unified execution has a configured Airbender machine execution. -/
theorem unified_sail : UnifiedSailClaim := by
  intro trace workers initial cells program inits boot romSetup tables noSpecial stream accepted
  exact Proven.Equiv.sail_realizes
    (unified trace workers initial cells program inits boot romSetup tables noSpecial stream accepted)

end Airbender.Trace.Machine
