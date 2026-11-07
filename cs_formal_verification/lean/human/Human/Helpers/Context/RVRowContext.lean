import Human.Helpers.Context.RowContext
import Human.Helpers.Memory.InitialImageRV

/-! RV-typed siblings of `WriteHistory` and `RowPosition` (`RowContext.lean`): the row's pre-state is an `RV.State`.
    Native writes: a register write sets the register (x0 reads 0 through `getReg`); a RAM write stores four bytes in
    RAM (`mem`) at any address (below `ROM_END`: shadow RAM) and never changes the ROM image (`rom`). -/

namespace Airbender.Trace
open Arithmetic

/-- RV sibling of `Cell.write`: the state after writing `value` to `cell`. A RAM cell is RAM at any address (below
    `ROM_END`: shadow RAM, which no LOAD reads); STORE's rejection below `ROM_END` is `RV.step`'s, not the memory
    argument's. Never `none`. -/
def Cell.writeRV (cell : Cell) (value : BitVec 32) (before : RV.State) : Option RV.State :=
  match cell with
  | .register index => some (before.setReg index value)
  | .ram address => some (before.store address value 4)

/-- RV update for one native port. A port whose value equals the cell's current RV value leaves the state unchanged
    (reads are not replayed: a read-only port has `writeCode = readCode`, so it changes nothing). Otherwise the
    update is `Cell.writeRV`. ROM-store rejection is RV.step's store rule together with the circuit's store check. -/
def Cell.applyRV (cell : Cell) (value : BitVec 32) (before : RV.State) : Option RV.State :=
  if cell.readRV before = some value then some before else cell.writeRV value before

/-- RV sibling of `WriteHistory`: applies the native `(address, value)` ports in list order (tail first) to tracked
    RV cells with `Cell.applyRV` (read-only ports leave the state unchanged). -/
inductive RVWriteHistory (cells : List Cell) : List (Nat × Nat) → RV.State → RV.State → Prop where
  | nil (before : RV.State) : RVWriteHistory cells [] before before
  | cons {address value rest before middle after}
      (past : RVWriteHistory cells rest before middle)
      (cell : Cell) (member : cell ∈ cells) (atAddress : cell.addressCode = address)
      (write : cell.applyRV (Word.mk (Nat.unpair value).1 (Nat.unpair value).2).toBitVec middle = some after) :
      RVWriteHistory cells ((address, value) :: rest) before after

/-- RV sibling of `RowPosition`: locate `row` in `trace` and interpret its pre-state as `before : RV.State`. `initial`
    is the public starting state; the earlier rows' writes are applied to it, then the PC is set to the row's start PC.
    `RV.State.input` stays the starting input. A CSR 0x7C0 read (`csrrw rd, 0x7c0, x0`) is an oracle read: it is a write
    of an unconstrained value to `rd`, so a row's pre-state carries that value in its registers, and its input stream is
    not advanced here. A run-level statement, not this per-row relation, ties the consumed values to the input list.
    Rows that never read the oracle (ADD/SUB/ADDI/LUI/AUIPC) are unaffected. -/
def RVRowPosition {Kind : Type} [CircuitLayout Kind] {p : Nat} [Fact p.Prime]
    (trace : Data p Kind) (initial : RV.State) (cells : List Cell)
    (row : Row p Kind) (before : RV.State) : Prop :=
  ∃ newer older middle,
    (newer ++ row :: older).Perm trace.rows ∧
    (newer ++ row :: older).Pairwise (fun a b => b.clock < a.clock) ∧
    RVWriteHistory cells (older.flatMap rowWriteValues) initial middle ∧
    before = { middle with pc := row.start.word.toBitVec }

end Airbender.Trace
