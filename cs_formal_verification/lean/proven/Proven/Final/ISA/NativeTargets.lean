import Human.ISA.Sail.NativeTargets
import Proven.ISA.Equiv.WholeRun
import Proven.Final.Compiler.NativeMachine

namespace Airbender.Trace.Machine.Native

/-- Cached native full-machine certificates give a complete configured machine run. -/
theorem unrolled_full_from_native_sail : UnrolledFullFromNativeSailClaim := by
  intro trace workers initial cells program inits tables boot wordSetup subwordSetup workerSetup
    noSpecial noMop stream bound covers certificates arguments
  exact Proven.Equiv.sail_realizes
    (unrolled_full_from_native trace workers initial cells program inits tables boot wordSetup subwordSetup
      workerSetup noSpecial noMop stream bound covers certificates arguments)

/-- Cached native reduced-machine certificates give a complete configured machine run. -/
theorem unrolled_reduced_from_native_sail : UnrolledReducedFromNativeSailClaim := by
  intro trace workers initial cells program inits tables boot wordSetup subwordSetup workerSetup
    stream bound covers certificates arguments
  exact Proven.Equiv.sail_realizes
    (unrolled_reduced_from_native trace workers initial cells program inits tables boot wordSetup subwordSetup
      workerSetup stream bound covers certificates arguments)

/-- Cached native unified-machine certificates give a complete configured machine run. -/
theorem unified_from_native_sail : UnifiedFromNativeSailClaim := by
  intro trace workers initial cells program inits tables boot setup workerSetup noSpecial stream bound certificates arguments
  exact Proven.Equiv.sail_realizes
    (unified_from_native trace workers initial cells program inits tables boot setup workerSetup
      noSpecial stream bound certificates arguments)

end Airbender.Trace.Machine.Native
