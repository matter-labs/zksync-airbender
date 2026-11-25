module
public import Human.Helpers.Memory.InitialImageRV
public import Human.ISA.RV32
public import Human.Helpers.Core.BabyBearPrime

@[expose] public section

/-! The shared conclusion of trace-level claims over our RV32 spec: an accepted trace is a run of `RV.run` from the
    public starting state `initial : RV.State`. -/

namespace Airbender.Trace
open Arithmetic

/-- Observable agreement between an RV execution and the terminal tokens of a trace over its host field. -/
def RealizesRun {Kind : Type} [CircuitLayout Kind] {p : Nat} [Fact p.Prime] (trace : Data p Kind)
    (initial : RV.State) (cells : List Cell) (consumed : Nat) (result : Option RV.State) : Prop :=
  ∃ after, result = some after ∧ after.input = initial.input.drop consumed ∧
    after.pc = trace.terminal.word.toBitVec ∧
    ∀ sink ∈ trace.terminalMemory, ∃ cell ∈ cells, cell.addressCode = sink.address ∧
      cell.readRV after = some sink.word.toBitVec

/-- An accepted trace reaches its terminal values after finitely many RV steps. -/
def RVRealizes {Kind : Type} [CircuitLayout Kind] {p : Nat} [Fact p.Prime] (trace : Data p Kind)
    (initial : RV.State) (cells : List Cell) (consumed : Nat := 0) : Prop :=
  ∃ n, RealizesRun trace initial cells consumed (RV.run n initial)

end Airbender.Trace
