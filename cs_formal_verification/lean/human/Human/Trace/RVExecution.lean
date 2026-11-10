module
public import Human.Helpers.Memory.InitialImageRV
public import Human.ISA.RV32
public import Human.Helpers.Core.BabyBearPrime

@[expose] public section

/-! The shared conclusion of trace-level claims over our RV32 spec: an accepted trace is a run of `RV.run` from the
    public starting state `initial : RV.State`. -/

namespace Airbender.Trace
open Arithmetic

/-- An accepted trace is a run of our spec: some number of `RV.step`s from `initial` reach a state whose PC and
    tracked cells (registers and RAM, shadow RAM included) are the trace's terminal ones. This definition adds no
    assumptions. -/
def RVRealizes {Kind : Type} [CircuitLayout Kind] {p : Nat} [Fact p.Prime] (trace : Data p Kind)
    (initial : RV.State) (cells : List Cell) : Prop :=
  ∃ n after, RV.run n initial = some after ∧ after.pc = trace.terminal.word.toBitVec ∧
    ∀ sink ∈ trace.terminalMemory, ∃ cell ∈ cells, cell.addressCode = sink.address ∧
      cell.readRV after = some sink.word.toBitVec

/-- The shape of the whole-trace claims over a public program: every accepted trace whose public boundary meets
    `inputs` and whose rows are `decoded` against the program is a run of our spec (`RVRealizes`). -/
def RVTraceSoundness {Kind : Type} [CircuitLayout Kind] {Program : Type}
    (inputs : Data babyBearModulus Kind → RV.State → List Cell → Program → Prop)
    (decoded : Data babyBearModulus Kind → Program → Prop) : Prop :=
  ∀ {trace : Data babyBearModulus Kind} {initial : RV.State} {cells : List Cell} {program : Program},
    inputs trace initial cells program → Accepted trace → decoded trace program → RVRealizes trace initial cells

end Airbender.Trace
