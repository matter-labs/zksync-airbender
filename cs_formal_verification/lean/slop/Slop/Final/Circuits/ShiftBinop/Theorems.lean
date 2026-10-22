import Slop.ShiftBinop
import Slop.ShiftBinop.RowClaims
import Slop.ShiftBinop.TraceSoundness
import Slop.ShiftBinop.Shifts
import Slop.ShiftBinop.Trace
import Slop.ShiftBinop.Decoder
import Slop.BabyBear

namespace Airbender.ShiftBinop

/-- Original Sail bitwise, shift and REV8 execution, with register and PC effects.
    Shared initialized history discharges all local range/read/decoder interfaces. -/
theorem soundness {p : Nat} [Fact p.Prime]
    (hp : 536870912 ≤ p) (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    (trace : Trace.PooledTrace p) (initial : Reference.RiscV.Sail.State)
    (cells : List Trace.Cell) (program : List Trace.PooledProgramEntry) :
    InterfaceAssumptions trace initial cells program →
    Properties.Soundness (circuitModel trace initial cells program).relation spec :=
  Proofs.pooled_row_soundness hp clockInverse trace initial cells program

theorem babyBear_soundness
    (trace : Trace.PooledTrace babyBearModulus) (initial : Reference.RiscV.Sail.State)
    (cells : List Trace.Cell) (program : List Trace.PooledProgramEntry) :
    InterfaceAssumptions trace initial cells program →
    Properties.Soundness (circuitModel trace initial cells program).relation spec :=
  soundness (by decide) (by decide) trace initial cells program

end Airbender.ShiftBinop
