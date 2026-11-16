module
public import Proven.NonVacuous.DynamicCopyLoop.Accepted
public import Proven.NonVacuous.DynamicCopyLoop.NativeSetup
public import Proven.NonVacuous.DynamicCopyLoop.WorkerCertificates
public import Proven.NonVacuous.DynamicCopyLoop.CpuCertificates
public import Human.Compiler.NativeTargets

@[expose] public section
namespace Airbender.NonVacuous.DynamicCopyLoop
open Airbender.Compiler
set_option warningAsError true

/-- The native certificates retain every submitted CPU occurrence in loop order. -/
noncomputable def certificates : List (UnifiedLogicalRowCertificate tables) :=
  (List.finRange 16).map cpuCertificate

/-- Full native CPU and worker certificates retain the independent exact matching interfaces. -/
theorem native_arguments : UnifiedNativeArguments tables certificates trace workers := by
  refine ⟨worker_rows_certified, ?_, states, request_matching, memory_matching⟩
  change machineRows = _
  simp only [certificates, List.map_map]
  rfl

/-- Sixteen CPU occurrences and two COPY workers meet every native target premise. -/
theorem native_witness : Trace.Machine.Native.UnifiedFromNativeSatisfiableClaim :=
  ⟨trace, workers, initial, cells, program, inits, tables, row_counts.1, row_counts.2.1,
    row_counts.2.2, boot, rfl, rfl, no_special, stream_ports, tables_bound, certificates, native_arguments⟩

end Airbender.NonVacuous.DynamicCopyLoop

namespace Airbender.NonVacuous.Machine

/-- The unified native target has a public boot witness with a loop and two bigint calls. -/
theorem unified_native : Trace.Machine.Native.UnifiedFromNativeSatisfiableClaim :=
  DynamicCopyLoop.native_witness

end Airbender.NonVacuous.Machine
