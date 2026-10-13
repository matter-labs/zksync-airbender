import Airbender.Proofs.ShiftBinop
import Airbender.Proofs.ShiftBinop.RowClaims
import Airbender.Proofs.ShiftBinop.TraceSoundness
import Airbender.Proofs.ShiftBinop.Shifts
import Airbender.Proofs.ShiftBinop.Trace
import Airbender.Proofs.ShiftBinop.Decoder
import Airbender.Proofs.BabyBear

namespace Airbender.ShiftBinop

/-- Original Sail bitwise, shift and REV8 execution, with register and PC effects.
    Shared initialized history discharges all local range/read/decoder interfaces. -/
theorem soundness {p : Nat} [Fact p.Prime]
    [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]
    (hp : 536870912 ≤ p) (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    (trace : Trace.PooledTrace p) (initial : Reference.RiscV.Sail.State)
    (cells : List Trace.Cell) (program : List Trace.PooledProgramEntry) :
    InterfaceAssumptions trace initial cells program →
    Properties.Soundness (circuitModel trace initial cells program).relation spec :=
  Proofs.pooled_row_soundness hp clockInverse trace initial cells program

theorem babyBear_soundness [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]
    (trace : Trace.PooledTrace babyBearModulus) (initial : Reference.RiscV.Sail.State)
    (cells : List Trace.Cell) (program : List Trace.PooledProgramEntry) :
    InterfaceAssumptions trace initial cells program →
    Properties.Soundness (circuitModel trace initial cells program).relation spec :=
  soundness (by decide) (by decide) trace initial cells program

end Airbender.ShiftBinop
