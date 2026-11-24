module
public import Human.Helpers.Context.Columns
public import Human.Helpers.Memory.IndirectPorts
public import Mathlib.Data.Nat.Pairing
public import CleanCore.Utils.OfflineMemory
public import Human.Helpers.Memory.Ports

/-! Definitions only the proofs use, moved from `human/Human/Helpers/Memory/Ports.lean` (no claim states them). -/

@[expose] public section
namespace Airbender.Trace
@[simp] theorem WordColumns.evaluate_u16 {p : Nat} (c : Vector Nat 2) (w : Nat → ZMod p) :
    (WordColumns.u16 c).evaluate w = #v[w c[0], w c[1]] := by rfl
@[simp] theorem WordColumns.code_u16 {p : Nat} (columns : Vector Nat 2) (w : Nat → ZMod p) :
    (WordColumns.u16 columns).code w = pairCode w columns := by rfl
/-- The actual port projected into Clean's memory-access object. The timestamp
    is the row's initial clock plus the imported in-cycle offset. -/
def MemoryPort.event {p : Nat} (port : MemoryPort) (columns : TraceColumns)
    (w : Nat → ZMod p) : MemoryAccess :=
  ((decodeTimestamp w columns.initialTime).value + port.clock.offset,
    port.address.code w, port.readCode w, port.writeCode w)
end Airbender.Trace
