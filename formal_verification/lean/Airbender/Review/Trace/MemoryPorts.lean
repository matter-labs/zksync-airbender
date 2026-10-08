import Airbender.Review.Trace.Columns
import Mathlib.Data.Nat.Pairing
import Clean.Utils.OfflineMemory

namespace Airbender.Trace

/-- Native register/RAM address metadata. The mixed selector has Rust's polarity:
    a true register selector encodes space zero; a true RAM selector encodes one. -/
inductive MemoryAddress where
  | constantRegister (index : Nat)
  | register (column : Nat)
  | mixed (selector : Nat) (registerOnTrue : Bool) (columns : Vector Nat 2)
  deriving DecidableEq

/-- Read/write columns and the same clock descriptor used by the clock proofs.
    A readonly port writes its read value back with a fresh timestamp. -/
structure MemoryPort where
  clock : TimestampPort
  address : MemoryAddress
  readColumns : Vector Nat 2
  writeColumns : Option (Vector Nat 2)
  deriving DecidableEq

/-- Injective coding for Clean's natural-valued memory model. Keep limbs separate
    until their bounds are proved; combining unbounded limbs as a word loses data. -/
def pairCode {p : Nat} (w : Nat → ZMod p) (columns : Vector Nat 2) : Nat :=
  Nat.pair (w columns[0]).val (w columns[1]).val

def MemoryAddress.code {p : Nat} (address : MemoryAddress) (w : Nat → ZMod p) : Nat :=
  match address with
  | .constantRegister index => Nat.pair 0 (Nat.pair index 0)
  | .register column => Nat.pair 0 (Nat.pair (w column).val 0)
  | .mixed selector registerOnTrue columns =>
    let space := if registerOnTrue then 1 - w selector else w selector
    Nat.pair space.val (pairCode w columns)

def MemoryPort.readCode {p : Nat} (port : MemoryPort) (w : Nat → ZMod p) : Nat :=
  pairCode w port.readColumns

def MemoryPort.writeCode {p : Nat} (port : MemoryPort) (w : Nat → ZMod p) : Nat :=
  pairCode w (port.writeColumns.getD port.readColumns)

/-- The actual port projected into Clean's memory-access object. The timestamp
    is the row's initial clock plus the imported in-cycle offset. -/
def MemoryPort.event {p : Nat} (port : MemoryPort) (columns : TraceColumns)
    (w : Nat → ZMod p) : MemoryAccess :=
  ((decodeTimestamp w columns.initialTime).value + port.clock.offset,
    port.address.code w, port.readCode w, port.writeCode w)

end Airbender.Trace
