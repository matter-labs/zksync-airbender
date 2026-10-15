import Airbender.Review.Helpers.Memory.SailHistory

namespace Airbender.Trace
open Reference.RiscV.Sail Reference.Sail

/-- Execute a finite list of typed Sail cell writes, tail first. This relation
    contains the entire resulting Sail state, including the unchanged frame;
    it has no circuit assignment, native port or memory-argument premise. -/
inductive CellWrites : List (Cell × BitVec 32) → State → State → Prop where
  | nil (before) : CellWrites [] before before
  | cons {cell value rest before middle after}
      (past : CellWrites rest before middle)
      (write : run (cell.write value) middle = .ok () after) :
      CellWrites ((cell, value) :: rest) before after

/-- Full architectural effect of an atomic project call. Every declared write
    occurs once and no other cell is written. The order is unobservable for the
    distinct aligned destinations admitted by the call ABI. Readonly cells may
    be rewritten with their original values, as in the native transfer model. -/
def AtomicWrites (writes : List (Cell × BitVec 32)) (before after : State) : Prop :=
  ∃ actual, (actual.map fun entry => (entry.1.addressCode, entry.2)).Perm
    (writes.map fun entry => (entry.1.addressCode, entry.2)) ∧ CellWrites actual before after

end Airbender.Trace
