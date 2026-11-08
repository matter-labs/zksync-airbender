module
public import Human.Helpers.Memory.InitialImage
public import Human.Helpers.Memory.History

@[expose] public section

namespace Airbender.Trace
open Arithmetic

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

end Airbender.Trace
