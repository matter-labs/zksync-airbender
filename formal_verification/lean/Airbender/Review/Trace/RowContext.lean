import Airbender.Review.Trace.Execution

namespace Airbender.Trace
open Arithmetic Reference.RiscV.Sail Reference.Sail

/-- Map native writes to Sail state. This checks no read value: those must be
    proved from the accepted, initialized memory argument. Lists run tail first. -/
inductive WriteHistory (cells : List Cell) : List (Nat × Nat) → State → State → Prop where
  | nil (before) : WriteHistory cells [] before before
  | cons {address value rest before middle after}
      (past : WriteHistory cells rest before middle)
      (cell : Cell) (member : cell ∈ cells) (atAddress : cell.addressCode = address)
      (write : run (cell.write (Word.mk (Nat.unpair value).1 (Nat.unpair value).2).toBitVec)
        middle = .ok () after) :
      WriteHistory cells ((address, value) :: rest) before after

def rowWriteValues {Kind : Type} [CircuitLayout Kind] (row : Row p Kind) : List (Nat × Nat) :=
  row.writes.reverse.map fun token => (token.address, token.value)

/-- Represent the input state at this row's position in the native trace.
    Earlier writes supply GPR/RAM state; native start-PC supplies control state.
    No successful read, limb bound or ISA execution is required here. -/
def RowPosition {Kind : Type} [CircuitLayout Kind] {p : Nat} [Fact p.Prime]
    (trace : Data p Kind) (initial : State) (cells : List Cell)
    (row : Row p Kind) (before : State) : Prop :=
  ∃ newer older middle,
    (newer ++ row :: older).Perm trace.rows ∧
    (newer ++ row :: older).Pairwise (fun a b => b.clock < a.clock) ∧
    WriteHistory cells (older.flatMap rowWriteValues) initial middle ∧
    before = { middle with regs := middle.regs.insert .nextPC row.start.word.toBitVec |>.insert .PC row.start.word.toBitVec }

end Airbender.Trace
