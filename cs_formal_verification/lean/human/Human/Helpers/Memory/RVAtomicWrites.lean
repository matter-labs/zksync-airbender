import Human.Helpers.Context.RVRowContext

/-! RV sibling of `AtomicWrites.lean`: a finite list of typed cell writes executed on an `RV.State` by `Cell.applyRV`
    (a RAM cell is RAM at any address, INCLUDING THE SHADOW RAM BELOW `ROM_END`; writing a cell's current value
    leaves the state unchanged, as in `RVHistory`). -/

namespace Airbender.Trace

/-- RV sibling of `CellWrites`: execute typed RV cell writes, tail first. -/
inductive RVCellWrites : List (Cell × BitVec 32) → RV.State → RV.State → Prop where
  | nil (before : RV.State) : RVCellWrites [] before before
  | cons {cell : Cell} {value : BitVec 32} {rest : List (Cell × BitVec 32)} {before middle after : RV.State}
      (past : RVCellWrites rest before middle)
      (write : cell.applyRV value middle = some after) :
      RVCellWrites ((cell, value) :: rest) before after

/-- RV sibling of `AtomicWrites`: every declared write occurs once (in some order) and no other cell is written. -/
def RVAtomicWrites (writes : List (Cell × BitVec 32)) (before after : RV.State) : Prop :=
  ∃ actual, (actual.map fun entry => (entry.1.addressCode, entry.2)).Perm
    (writes.map fun entry => (entry.1.addressCode, entry.2)) ∧ RVCellWrites actual before after

end Airbender.Trace
