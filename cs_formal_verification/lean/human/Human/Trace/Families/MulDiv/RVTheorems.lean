module
public import Human.Trace.RVExecution
public import Human.Helpers.Context.RVBoundary
public import Human.Helpers.Context.Registries.MulDiv
public import Human.Circuits.MulDiv.RVDecoder
public import Human.Helpers.Core.BabyBearPrime

@[expose] public section

/-! Trace claim: the accepted rows are a run of our spec (`RV.run`) from the
    public starting state `initial : RV.State`. Proven in `proven/Proven/Final/Trace/Families/MulDiv/RVTheorems.lean`
    (checked by verify.sh). -/

namespace Airbender.MulDiv
open Trace

/-- Every row's decoder query is in the family table built from the RV program. Logical
    membership; lookup enforcement is external. -/
def RVDecoded {p : Nat} [Fact p.Prime] (trace : NativeTrace p) (program : List RVProgramEntry) : Prop :=
  ∀ row ∈ trace.rows, (rvDecoderTable program).Contains #[] (decoderQuery row.assignment)

/-- Public inputs: `RVNativeInputs rvDecoderFields`. -/
abbrev RVExecutionInputs {p : Nat} [Fact p.Prime] (trace : NativeTrace p) (initial : RV.State)
    (cells : List Cell) (program : List RVProgramEntry) : Prop :=
  RVNativeInputs rvDecoderFields trace initial cells program

/-- Publicly fetched MUL/MULHU/DIVU/REMU rows, in native time order, are a run of `RV.step` from `initial` reaching
    the terminal PC and cell values. Public initialization and logical matching/membership remain explicit. -/
def RVTraceSoundnessClaim : Prop :=
  ∀ {trace : NativeTrace babyBearModulus} {initial : RV.State} {cells : List Cell} {program : List RVProgramEntry},
    RVExecutionInputs trace initial cells program → Accepted trace → RVDecoded trace program →
      RVRealizes trace initial cells

/-- The assumptions of `RVTraceSoundnessClaim` can be met, by a trace with a row. -/
def RVTraceSoundnessSatisfiableClaim : Prop :=
  ∃ (trace : NativeTrace babyBearModulus) (initial : RV.State) (cells : List Cell) (program : List RVProgramEntry),
    RVExecutionInputs trace initial cells program ∧ Accepted trace ∧ RVDecoded trace program ∧ trace.rows ≠ []

end Airbender.MulDiv
