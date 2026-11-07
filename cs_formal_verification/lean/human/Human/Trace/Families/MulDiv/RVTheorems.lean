import Human.Trace.RVExecution
import Human.Helpers.Context.RVBoundary
import Human.Helpers.Context.Registries.MulDiv
import Human.Circuits.MulDiv.RVDecoder

/-! RV32 twin of `TraceSoundnessClaim` (`Theorems.lean`): the accepted rows are a run of our spec (`RV.run`) from the
    public starting state `initial : RV.State`. Proven in `slop/Slop/Final/Trace/Families/MulDiv/RVTheorems.lean`
    (checked by verify.sh). -/

namespace Airbender.MulDiv
open Trace

/-- RV twin of `Decoded`: every row's decoder query is in the family table built from the RV program. Logical
    membership; lookup enforcement is external. -/
def RVDecoded {p : Nat} [Fact p.Prime] (trace : NativeTrace p) (program : List RVProgramEntry) : Prop :=
  ∀ row ∈ trace.rows, (rvDecoderTable program).Contains #[] (decoderQuery row.assignment)

/-- RV twin of `ExecutionBoundary` (`NativeInputs decoderFields` without the Sail-only `Configured`). -/
abbrev RVExecutionInputs {p : Nat} [Fact p.Prime] (trace : NativeTrace p) (initial : RV.State)
    (cells : List Cell) (program : List RVProgramEntry) : Prop :=
  RVNativeInputs rvDecoderFields trace initial cells program

/-- Publicly fetched MUL/MULHU/DIVU/REMU rows, in native time order, are a run of `RV.step` from `initial` reaching
    the terminal PC and cell values. Public initialization and logical matching/membership remain explicit. -/
def RVTraceSoundnessClaim : Prop :=
  ∀ {p : Nat} [Fact p.Prime] (hp : 536870912 ≤ p) (inverse : (-30720 : ZMod p) * 65536 = 1) (clockInverse : (-3840 : ZMod p) * 524288 = 1) {trace : NativeTrace p} {initial : RV.State} {cells : List Trace.Cell} {program : List RVProgramEntry} (inputs : RVExecutionInputs trace initial cells program) (accepted : Trace.Accepted trace) (decoded : RVDecoded trace program),
    Trace.RVRealizes trace initial cells

end Airbender.MulDiv
