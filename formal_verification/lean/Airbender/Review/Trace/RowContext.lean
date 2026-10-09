import Airbender.Review.Trace.Execution

namespace Airbender.Trace
open Arithmetic Reference.RiscV.Sail Reference.Sail

/-- Interpret native `(address, value)` writes as updates to tracked Sail cells.
    `cells` is the public register/RAM domain; values use the same pair coding
    as `MemoryToken`. Lists run tail first, matching descending native clocks.

    This relation applies writes only. The accepted, initialized memory history
    separately proves the reads used by the instruction. -/
inductive WriteHistory (cells : List Cell) : List (Nat × Nat) → State → State → Prop where
  | nil (before) : WriteHistory cells [] before before
  | cons {address value rest before middle after}
      (past : WriteHistory cells rest before middle)
      (cell : Cell) (member : cell ∈ cells) (atAddress : cell.addressCode = address)
      (write : run (cell.write (Word.mk (Nat.unpair value).1 (Nat.unpair value).2).toBitVec)
        middle = .ok () after) :
      WriteHistory cells ((address, value) :: rest) before after

/-- This row's writes in reverse port order. `WriteHistory` applies the tail
    first, so their Sail effects occur in the original native port order. -/
def rowWriteValues {Kind : Type} [CircuitLayout Kind] (row : Row p Kind) : List (Nat × Nat) :=
  row.writes.reverse.map fun token => (token.address, token.value)

/-- Locate `row` in `trace` and interpret its pre-state as Sail state `before`.
    `initial` is the public starting state, and `cells` lists tracked registers/RAM.

    `newer ++ row :: older` orders all rows by descending clock. Apply the
    writes of `older` to `initial`, then set Sail's PC and nextPC to this row's
    imported start PC. This yields the state used by each circuit's `TraceMapping`.
    Reads, bounds and successful ISA execution are conclusions of soundness. -/
def RowPosition {Kind : Type} [CircuitLayout Kind] {p : Nat} [Fact p.Prime]
    (trace : Data p Kind) (initial : State) (cells : List Cell)
    (row : Row p Kind) (before : State) : Prop :=
  ∃ newer older middle,
    (newer ++ row :: older).Perm trace.rows ∧
    (newer ++ row :: older).Pairwise (fun a b => b.clock < a.clock) ∧
    WriteHistory cells (older.flatMap rowWriteValues) initial middle ∧
    before = { middle with regs := middle.regs.insert .nextPC row.start.word.toBitVec |>.insert .PC row.start.word.toBitVec }

end Airbender.Trace
