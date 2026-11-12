module
public import Human.Trace.RVExecution
public import Human.Helpers.Context.RVBoundary
public import Human.Helpers.Context.Registries.JumpBranchSlt
public import Human.Circuits.JumpBranchSlt.RVDecoder
public import Human.Helpers.Core.BabyBearPrime

@[expose] public section

/-! Trace claim: the accepted rows are a run of our spec (`RV.run`) from the
    public starting state `initial : RV.State`. Proven in `proven/Proven/Final/Trace/Families/JumpBranchSlt/RVTheorems.lean`
    (checked by verify.sh). -/

namespace Airbender.JumpBranchSlt
open Trace

/-- Every row's decoder query is in the family table built from the RV program. Logical
    membership; lookup enforcement is external. -/
def RVDecoded {p : Nat} [Fact p.Prime] (trace : NativeTrace p) (program : List RVProgramEntry) : Prop :=
  ∀ row ∈ trace.rows, (rvDecoderTable program).Contains #[] (decoderQuery row.assignment)

/-- Public inputs (`RVNativeInputs`). No alignment premise on the initial PC is needed: the RV program
    table's fetch guard aligns every row's PC. -/
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
  ∀ {trace : NativeTrace babyBearModulus} {initial : RV.State} {cells : List Cell} {program : List RVProgramEntry},
    RVExecutionInputs trace initial cells program → Accepted trace → RVDecoded trace program →
      RVRealizes trace initial cells

/-- The assumptions of `RVTraceSoundnessClaim` can be met, by a trace with a row. -/
def RVTraceSoundnessSatisfiableClaim : Prop :=
  ∃ (trace : NativeTrace babyBearModulus) (initial : RV.State) (cells : List Cell) (program : List RVProgramEntry),
    RVExecutionInputs trace initial cells program ∧ Accepted trace ∧ RVDecoded trace program ∧ trace.rows ≠ []

end Airbender.JumpBranchSlt
