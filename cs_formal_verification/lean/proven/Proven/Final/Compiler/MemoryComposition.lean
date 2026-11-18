module
public import Proven.Compiler.MemoryCompositionNative
public import Proven.Final.Compiler.NativeMachine

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler
open Trace Trace.Machine NativeMemory

/-- The native certificates place every token in one address class, so the single RAM permutation of an unrolled
    trace splits into its three relations. -/
theorem unrolled_memory_composition : UnrolledMemoryCompositionClaim := by
  intro config trace workers initial cells program layout inits tables certificates unrolled boot bound covers rows
    production
  obtain ⟨addresses, image⟩ := boot.programImage
  have boundary := boot_architectural boot
  have states := production_states trace workers boundary (unrolled_certified_spaces bound covers rows) production
  have classes := unrolled_certified_classes unrolled image bound covers rows boot.initialBoundary states
  exact (production_iff trace workers unrolledCaller (fun row => Delegation.Requests.caller row.assignment)
    Delegation.Caller.machinePorts boundary classes).mp production

/-- The native certificates place every token in one address class, so the single RAM permutation of a unified
    trace splits into its three relations. -/
theorem unified_memory_composition : UnifiedMemoryCompositionClaim := by
  intro trace workers initial cells program layout inits tables certificates boot bound rows production
  obtain ⟨addresses, image⟩ := boot.programImage
  have boundary := boot_architectural boot
  have states := production_states trace workers boundary (unified_certified_spaces bound rows) production
  have classes := unified_certified_classes image bound rows boot.initialBoundary states
  exact (production_iff trace workers unifiedCaller (fun row => UnifiedReduced.Caller.request row.assignment)
    UnifiedReduced.Caller.machinePorts boundary classes).mp production

/-- The one-row ADD trace meets the unrolled premises: its three relations give the single RAM permutation. -/
theorem unrolled_memory_composition_satisfiable : UnrolledMemoryCompositionSatisfiableClaim := by
  obtain ⟨trace, workers, initial, cells, program, inits, tables, boot, _, _, bound, covers, certificates, arguments,
    length, _, _⟩ := Trace.Machine.Native.unrolled_full_from_native_satisfiable
  exact ⟨.unrolledFullUnsigned, trace, workers, initial, cells, program, InitsTeardowns.importedLayout, inits, tables,
    certificates, by decide, boot, bound, covers, arguments.rows,
    unrolled_native_production (by decide) boot bound covers arguments, length⟩

/-- A loop with sixteen unified rows and two bigint calls meets the unified premises: its three relations give the
    single RAM permutation. -/
theorem unified_memory_composition_satisfiable : UnifiedMemoryCompositionSatisfiableClaim := by
  obtain ⟨trace, workers, initial, cells, program, inits, tables, boot, _, _, bound, certificates, arguments,
    length, standard, _⟩ := Trace.Machine.Native.unified_from_native_satisfiable
  exact ⟨trace, workers, initial, cells, program, InitsTeardowns.unifiedLayout, inits, tables, certificates, boot,
    bound, arguments.rows, unified_native_production boot bound arguments, length, standard⟩

end Airbender.Compiler
