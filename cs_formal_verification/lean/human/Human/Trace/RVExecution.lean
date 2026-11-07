import Human.Helpers.Memory.InitialImageRV
import Human.ISA.RV32

/-! The shared conclusion of trace-level claims over our RV32 spec: an accepted trace is a run of `RV.run` from the
    public starting state `initial : RV.State` (not a Sail execution). RV sibling of `Execution.lean`'s `Realizes`. -/

namespace Airbender.Trace
open Arithmetic

/-- RV sibling of `InitialProfile` (`Helpers/Memory/Initialization.lean`): PC 0, all registers 0, all tracked RAM 0
    (shadow RAM below `ROM_END` included, as the native seed). The ROM image (`rom`) holds the public program. -/
structure RVInitialProfile (initial : RV.State) (cells : List Cell) : Prop where
  pc : initial.pc = 0
  registers : ∀ index, (Cell.register index).readRV initial = some 0
  /-- All of RAM starts at 0, the shadow RAM below `ROM_END` included (`RV.State.RamStartsZero`). -/
  ram : initial.RamStartsZero

/-- An accepted trace is a run of our spec: some number of `RV.step`s from `initial` reach a state whose PC and
    tracked cells (registers and RAM, shadow RAM included) are the trace's terminal ones. This definition adds no
    assumptions. -/
def RVRealizes {Kind : Type} [CircuitLayout Kind] {p : Nat} [Fact p.Prime] (trace : Data p Kind)
    (initial : RV.State) (cells : List Cell) : Prop :=
  ∃ n after, RV.run n initial = some after ∧ after.pc = trace.terminal.word.toBitVec ∧
    ∀ sink ∈ trace.terminalMemory, ∃ cell ∈ cells, cell.addressCode = sink.address ∧
      cell.readRV after = some sink.word.toBitVec

end Airbender.Trace
