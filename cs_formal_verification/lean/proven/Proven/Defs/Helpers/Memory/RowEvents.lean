module
public import Human.Helpers.Memory.InitialImage
public import Proven.Defs.Helpers.Memory.History
public import Human.Helpers.Memory.RowEvents
public import Proven.Defs.Helpers.Memory.Ports

/-! Definitions only the proofs use, moved from `human/Human/Helpers/Memory/RowEvents.lean` (no claim states them). -/

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
end Airbender.Trace
