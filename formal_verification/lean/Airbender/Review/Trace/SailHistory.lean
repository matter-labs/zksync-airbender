import Airbender.Review.Trace.InitialImage
import Airbender.Review.Trace.MemoryHistory

namespace Airbender.Trace
open Arithmetic Reference.RiscV.Sail Reference.Sail

variable {Kind : Type} [CircuitLayout Kind]

/-- The imported ports, retaining their native order and shifted access clocks. -/
def nativeRowEvents (epoch : Nat) (columns : TraceColumns) (ports : Array MemoryPort)
    (w : Nat → ZMod p) : List MemoryAccess :=
  ports.toList.map fun port =>
    ((epoch + (port.event columns w).1, port.address.code w,
      port.readCode w, port.writeCode w) : MemoryAccess)

/-- Use this row's imported columns and ports at the supplied history epoch. -/
abbrev rowEvents (epoch : Nat) (row : Row p Kind) : List MemoryAccess :=
  nativeRowEvents epoch row.columns row.ports row.assignment

/-- Interpret Clean's injective value code as its canonical RV32 word. -/
def memoryWord (code : Nat) : BitVec 32 :=
  (Word.mk (Nat.unpair code).1 (Nat.unpair code).2).toBitVec

/-- A Sail state realizes the latest values of the existing Clean history.
    This is a representation relation, not another memory semantics. -/
def SailStateMatches (cells : List Cell) (history : TimestampSortedMemoryAccessList)
    (state : State) : Prop :=
  ∀ cell ∈ cells, cell.read state =
    .ok (memoryWord (MemoryAccessList.lastWriteValue history.val history.property cell.addressCode))
      state

/-- Actual Sail reads and writes for a reverse-chronological Clean access list.
    The tail executes first, as in Clean's online-consistency definition. -/
inductive SailHistory (cells : List Cell) : List MemoryAccess → State → State → Prop where
  | nil (before) : SailHistory cells [] before before
  | cons {event : MemoryAccess} {rest before middle after}
      (past : SailHistory cells rest before middle)
      (cell : Cell) (member : cell ∈ cells) (address : cell.addressCode = event.2.1)
      (read : cell.read middle = .ok (memoryWord event.2.2.1) middle)
      (write : run (cell.write (memoryWord event.2.2.2)) middle = .ok () after) :
      SailHistory cells (event :: rest) before after

/-- The actual two register insertions produced by successful Sail retirement.
    Used only to transport native histories through instruction boundaries. -/
def retiredState (state : State) (pc : BitVec 32) : State :=
  { state with regs := state.regs.insert .nextPC pc |>.insert .PC pc }

end Airbender.Trace
