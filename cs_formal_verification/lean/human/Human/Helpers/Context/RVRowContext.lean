import Human.Helpers.Context.RowContext
import Human.Helpers.Memory.InitialImageRV

/-! RV-typed siblings of `WriteHistory` and `RowPosition` (`RowContext.lean`): the row's pre-state is an `RV.State`.
    Native writes use the RV memory map: a register write sets the register (x0 reads 0 through `getReg`); a RAM write
    stores four bytes only where `RV.writable` allows (RAM, not ROM), the same failure as Sail's write in the configured
    memory map. -/

namespace Airbender.Trace
open Arithmetic

/-- RV sibling of `Cell.write`: the state after writing `value` to `cell`, or `none` when the write is not allowed. -/
def Cell.writeRV (cell : Cell) (value : BitVec 32) (before : RV.State) : Option RV.State :=
  match cell with
  | .register index => some (before.setReg index value)
  | .ram address => if RV.writable address 4 then some (before.store address value 4) else none

/-- RV sibling of `WriteHistory`: applies the native `(address, value)` writes in list order (tail first) to tracked
    RV cells. -/
inductive RVWriteHistory (cells : List Cell) : List (Nat × Nat) → RV.State → RV.State → Prop where
  | nil (before : RV.State) : RVWriteHistory cells [] before before
  | cons {address value rest before middle after}
      (past : RVWriteHistory cells rest before middle)
      (cell : Cell) (member : cell ∈ cells) (atAddress : cell.addressCode = address)
      (write : cell.writeRV (Word.mk (Nat.unpair value).1 (Nat.unpair value).2).toBitVec middle = some after) :
      RVWriteHistory cells ((address, value) :: rest) before after

/-- RV sibling of `RowPosition`: locate `row` in `trace` and interpret its pre-state as `before : RV.State`. `initial`
    is the public starting state; the earlier rows' writes are applied to it, then the PC is set to the row's start PC.
    `RV.State.input` is not advanced by earlier rows (no row of this family reads the input stream). -/
def RVRowPosition {Kind : Type} [CircuitLayout Kind] {p : Nat} [Fact p.Prime]
    (trace : Data p Kind) (initial : RV.State) (cells : List Cell)
    (row : Row p Kind) (before : RV.State) : Prop :=
  ∃ newer older middle,
    (newer ++ row :: older).Perm trace.rows ∧
    (newer ++ row :: older).Pairwise (fun a b => b.clock < a.clock) ∧
    RVWriteHistory cells (older.flatMap rowWriteValues) initial middle ∧
    before = { middle with pc := row.start.word.toBitVec }

end Airbender.Trace
