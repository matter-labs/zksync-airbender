module
public import Proven.NonVacuous.NativeMachines
public import Proven.NonVacuous.UnrolledNative.Certificates
public import Proven.NonVacuous.DynamicCopyLoop.Native
public import Human.Compiler.NativeTargets
public import Proven.Compiler.NativeAcceptance
public import Proven.Final.Trace.Machine.Unrolled
public import Proven.Final.Trace.Machine.Unified

@[expose] public section
namespace Airbender.Trace.Machine.Native
open Airbender.Compiler
set_option warningAsError true

/-- Current cached native certificates imply the full unsigned whole-machine run. -/
theorem unrolled_full_from_native : UnrolledFullFromNative := by
  intro trace workers initial cells program inits tables boot wordSetup subwordSetup workerSetup
    noSpecial stream bound covers certificates arguments
  exact Machine.unrolled_full_unsigned trace workers initial cells program inits boot wordSetup subwordSetup
    workerSetup noSpecial stream
    (NativeAcceptance.unrolled bound cells covers certificates trace workers arguments wordSetup subwordSetup workerSetup boot.initialBoundary)

/-- Current cached native certificates imply the reduced whole-machine run. -/
theorem unrolled_reduced_from_native : UnrolledReducedFromNative := by
  intro trace workers initial cells program inits tables boot wordSetup subwordSetup workerSetup
    stream bound covers certificates arguments
  exact Machine.unrolled_reduced trace workers initial cells program inits boot wordSetup subwordSetup
    workerSetup stream
    (NativeAcceptance.unrolled bound cells covers certificates trace workers arguments wordSetup subwordSetup workerSetup boot.initialBoundary)

/-- Current cached native certificates imply the unified whole-machine run. -/
theorem unified_from_native : UnifiedFromNative := by
  intro trace workers initial cells program inits tables boot setup workerSetup noSpecial stream bound certificates arguments
  exact Machine.unified trace workers initial cells program inits boot setup workerSetup noSpecial stream
    (NativeAcceptance.unified bound certificates trace workers arguments setup workerSetup boot.initialBoundary)

end Airbender.Trace.Machine.Native

namespace Airbender.Trace.Machine.Native

/-- One submitted ADD row meets every native boot and matching premise. -/
theorem unrolled_full_from_native_satisfiable : UnrolledFullFromNativeSatisfiableClaim := NonVacuous.Machine.full_native

/-- One submitted ADD row meets every native boot and matching premise. -/
theorem unrolled_reduced_from_native_satisfiable : UnrolledReducedFromNativeSatisfiableClaim := NonVacuous.Machine.reduced_native

/-- A loop with sixteen CPU rows and two bigint calls meets every native target premise. -/
theorem unified_from_native_satisfiable : UnifiedFromNativeSatisfiableClaim := NonVacuous.Machine.unified_native

end Airbender.Trace.Machine.Native
