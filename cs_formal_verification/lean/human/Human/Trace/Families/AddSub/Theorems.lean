import Human.Circuits.AddSub.Reference
import Human.Circuits.WordMemory.Model
import Human.Helpers.Core.BabyBearPrime
import Human.Helpers.Memory.Native
import Human.Helpers.Memory.SailHistory
import Human.Trace.Families.AddSub.Execution

-- The statements proven in slop/Slop/Final/Trace/Families/AddSub/Theorems.lean (checked by verify.sh).

namespace Airbender.Trace

/-- ADD/SUB and word-memory execution with unchanged Sail semantics.
    The loads condition excludes discarded LW instructions. -/
def SailSoundnessClaim : Prop :=
  ∀ [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception] {trace : Data babyBearModulus} {before : Reference.RiscV.Sail.State} {cells : List Cell} {program : List ProgramEntry} (inputs : ExecutionBoundary trace before cells program) (loads : NoDiscardedLoads program) (accepted : Accepted trace) (decoded : Decoded trace program),
    Realizes (SailStep program) trace before cells

/-- The same restricted trace with the named Airbender LW-to-x0 profile. -/
def AirbenderSoundnessClaim : Prop :=
  ∀ [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception] {trace : Data babyBearModulus} {before : Reference.RiscV.Sail.State} {cells : List Cell} {program : List ProgramEntry} (inputs : ExecutionBoundary trace before cells program) (accepted : Accepted trace) (decoded : Decoded trace program),
    Realizes (Step .airbender program) trace before cells

/-- Restricted execution from native boot, interpreting zero ROM shadows
    through the independent public bytes. -/
def NativeBootSoundnessClaim : Prop :=
  ∀ [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception] {trace : Data babyBearModulus} {before : Reference.RiscV.Sail.State} {cells : List Cell} {program : List ProgramEntry} (inputs : NativeBootBoundary trace before cells program) (accepted : Accepted trace) (decoded : Decoded trace program),
    Realizes (Step .airbender program) trace before cells (ROMView.token before)

end Airbender.Trace
