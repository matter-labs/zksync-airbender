import Airbender.Review.Trace.Families.AddSub.Execution
import Airbender.Proofs.Trace.Composition
import Airbender.Proofs.Trace.ROMView
import Airbender.Proofs.BabyBear

namespace Airbender.Trace

/-- ADD/SUB and word-memory execution with unchanged Sail semantics.
    The loads condition excludes discarded LW instructions. -/
theorem sail_soundness [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]
    {trace : Data babyBearModulus} {before : Reference.RiscV.Sail.State}
    {cells : List Cell} {program : List ProgramEntry}
    (inputs : ExecutionBoundary trace before cells program)
    (loads : NoDiscardedLoads program)
    (accepted : Accepted trace) (decoded : Decoded trace program) :
    Realizes (SailStep program) trace before cells :=
  Proofs.restricted_trace_execution .sail (by decide) (by decide) inputs (fun _ => loads) accepted decoded


/-- The same restricted trace with the named Airbender LW-to-x0 profile. -/
theorem airbender_soundness [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]
    {trace : Data babyBearModulus} {before : Reference.RiscV.Sail.State}
    {cells : List Cell} {program : List ProgramEntry}
    (inputs : ExecutionBoundary trace before cells program)
    (accepted : Accepted trace) (decoded : Decoded trace program) :
    Realizes (Step .airbender program) trace before cells :=
  Proofs.restricted_trace_execution .airbender (by decide) (by decide) inputs
    (by intro impossible; cases impossible) accepted decoded


/-- Restricted execution from native boot, interpreting zero ROM shadows
    through the independent public bytes. -/
theorem native_boot_soundness [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]
    {trace : Data babyBearModulus} {before : Reference.RiscV.Sail.State}
    {cells : List Cell} {program : List ProgramEntry}
    (inputs : NativeBootBoundary trace before cells program)
    (accepted : Accepted trace) (decoded : Decoded trace program) :
    Realizes (Step .airbender program) trace before cells (ROMView.token before) := by
  have clocks := ROMView.native_clocks (by decide) inputs.seed inputs.initial
  obtain ⟨after, execution, pc, terminal⟩ := airbender_soundness
    (ROMView.execution_boundary (by decide) inputs)
    (ROMView.accepted (by decide) (by decide) before accepted clocks inputs.seed)
    (ROMView.decoded before decoded)
  refine ⟨after, execution, pc, ?_⟩
  intro sink member
  have lifted := terminal (ROMView.token before sink) (List.mem_map_of_mem member)
  simpa only [ROMView.token_address, id_eq] using lifted

end Airbender.Trace
