module
public import Human.Helpers.Memory.InitialImageRV
public import Human.ISA.RV32
public import Human.Helpers.Core.BabyBearPrime

@[expose] public section

/-! The shared conclusion of trace-level claims over our RV32 spec: an accepted trace is a run of `RV.run` from the
    public starting state `initial : RV.State`. -/

namespace Airbender.Trace
open Arithmetic

/-- An accepted trace is a run of our RV32 spec (`RV.step`). The run consumes `consumed` input words.
    Its final PC and tracked registers and RAM, including shadow RAM, equal the trace terminal values. -/
def RVRealizes {Kind : Type} [CircuitLayout Kind] {p : Nat} [Fact p.Prime] (trace : Data p Kind)
    (initial : RV.State) (cells : List Cell) (consumed : Nat := 0) : Prop :=
  ∃ n after, RV.run n initial = some after ∧ after.input = initial.input.drop consumed ∧
    after.pc = trace.terminal.word.toBitVec ∧
    ∀ sink ∈ trace.terminalMemory, ∃ cell ∈ cells, cell.addressCode = sink.address ∧
      cell.readRV after = some sink.word.toBitVec

end Airbender.Trace
