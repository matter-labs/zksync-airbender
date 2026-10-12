import Airbender.Proofs.SubwordMemory.RowClaims
import Airbender.Proofs.SubwordMemory.TraceSoundness
import Airbender.Proofs.BabyBear
import Airbender.Proofs.SubwordMemory.Trace
import Airbender.Proofs.SubwordMemory.Composition

namespace Airbender.SubwordMemory
open _root_.Sail.ArchSem
variable [MemoryPlatform SailRV32.exception]

/-- RAM LB/LBU/LH/LHU/SB/SH execute the public program in native time order
    and reach its terminal PC and cell values. Global history supplies all input
    bounds and reads; the public boundary contains no per-row assumptions. -/
theorem ram_trace_soundness {p : Nat} [Fact p.Prime]
    (hp : 33554432 < p) (inverse : (-3840 : ZMod p) * 524288 = 1)
    {trace : NativeTrace p} {initial : Reference.RiscV.Sail.State} {cells : List Trace.Cell}
    {program : List ProgramEntry} (inputs : RAMInputs trace initial cells program)
    (accepted : Trace.Accepted trace) (decoded : Decoded trace program) :
    Trace.Realizes (SailStep program) trace initial cells :=
  Proofs.ram_trace_execution hp inverse inputs accepted decoded

/-- Original Sail subword loads/stores, aligned cell address, merged/register
    writes and PC effects. Shared history supplies all local ranges and reads. -/
theorem soundness {p : Nat} [Fact p.Prime] (hp : 536870912 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    (trace : Trace.PooledTrace p) (initial : Reference.RiscV.Sail.State)
    (cells : List Trace.Cell) (program : List Trace.PooledProgramEntry) :
    InterfaceAssumptions trace initial cells program →
    Properties.Soundness (circuitModel trace initial cells program).relation spec :=
  Proofs.pooled_row_soundness hp clockInverse trace initial cells program

theorem babyBear_soundness (trace : Trace.PooledTrace babyBearModulus)
    (initial : Reference.RiscV.Sail.State) (cells : List Trace.Cell)
    (program : List Trace.PooledProgramEntry) :
    InterfaceAssumptions trace initial cells program →
    Properties.Soundness (circuitModel trace initial cells program).relation spec :=
  soundness (by decide) (by decide) trace initial cells program

end Airbender.SubwordMemory
