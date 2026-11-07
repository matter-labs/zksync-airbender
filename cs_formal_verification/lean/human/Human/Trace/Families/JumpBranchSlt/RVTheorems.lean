import Human.Trace.RVExecution
import Human.Helpers.Context.RVBoundary
import Human.Helpers.Context.Registries.JumpBranchSlt
import Human.Circuits.JumpBranchSlt.RVDecoder

/-! RV32 twin of `TraceSoundnessClaim` (`Theorems.lean`): the accepted rows are a run of our spec (`RV.run`) from the
    public starting state `initial : RV.State`. Proven in `slop/Slop/Final/Trace/Families/JumpBranchSlt/RVTheorems.lean`
    (checked by verify.sh). -/

namespace Airbender.JumpBranchSlt
open Trace

/-- RV twin of `Decoded`: every row's decoder query is in the family table built from the RV program. Logical
    membership; lookup enforcement is external. -/
def RVDecoded {p : Nat} [Fact p.Prime] (trace : NativeTrace p) (program : List RVProgramEntry) : Prop :=
  ∀ row ∈ trace.rows, (rvDecoderTable program).Contains #[] (decoderQuery row.assignment)

/-- RV twin of `ExecutionBoundary`, without the Sail-only `Configured` and without `initialAligned` (the RV program
    table's fetch guard aligns every row's PC). -/
structure RVExecutionInputs {p : Nat} [Fact p.Prime] (trace : NativeTrace p) (initial : RV.State)
    (cells : List Cell) (program : List RVProgramEntry) : Prop
    extends RVNativeInputs rvDecoderFields trace initial cells program where
  /-- The terminal PC is a canonical word: the circuit does not range-check the outgoing PC's high limb, so the last
      row's target is bounded only through it. -/
  terminalCanonical : trace.terminal.word.Bounded

/-- Accepted comparison, branch and jump rows, in native time order, are a run of `RV.step` from `initial` reaching
    the terminal PC and register/cell values. Public initialization, canonical termination and logical
    matching/membership are the explicit boundaries in `RVExecutionInputs`, `Accepted` and `RVDecoded`. -/
def RVTraceSoundnessClaim : Prop :=
  ∀ {p : Nat} [Fact p.Prime] (hp : 4194304 ≤ p) (inverse : (-3840 : ZMod p) * 524288 = 1) {trace : NativeTrace p} {initial : RV.State} {cells : List Trace.Cell} {program : List RVProgramEntry} (inputs : RVExecutionInputs trace initial cells program) (accepted : Trace.Accepted trace) (decoded : RVDecoded trace program),
    Trace.RVRealizes trace initial cells

end Airbender.JumpBranchSlt
