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

/-- The imported Rust RAM word representation, before circuit bounds are proved. -/
inductive WordColumns where
  | zero
  | u16 (columns : Vector Nat 2)
  | u8 (columns : Vector Nat 4)
  deriving DecidableEq

instance : Coe (Vector Nat 2) WordColumns := ⟨WordColumns.u16⟩

/-- Rust's `RamWordRepresentation`: bytes are paired in the base field before
    the memory argument (`prover/src/gkr/prover/forward_loop/utils.rs`). Byte
    bounds must come from circuit lookups, not this metadata interpretation. -/
def WordColumns.evaluate {p : Nat} (columns : WordColumns) (w : Nat → ZMod p) :
    Vector (ZMod p) 2 :=
  match columns with
  | .zero => #v[0, 0]
  | .u16 c => #v[w c[0], w c[1]]
  | .u8 c => #v[w c[0] + 256 * w c[1], w c[2] + 256 * w c[3]]

@[simp] theorem WordColumns.evaluate_u16 {p : Nat} (c : Vector Nat 2) (w : Nat → ZMod p) :
    (WordColumns.u16 c).evaluate w = #v[w c[0], w c[1]] := rfl

def WordColumns.code {p : Nat} (columns : WordColumns) (w : Nat → ZMod p) : Nat :=
  Nat.pair (columns.evaluate w)[0].val (columns.evaluate w)[1].val

/-- A readonly port refreshes the same value; byte packing is shared with writes. -/
structure MemoryPort where
  clock : TimestampPort
  address : MemoryAddress
  readValue : WordColumns
  writeValue : Option WordColumns
  deriving DecidableEq

/-- Injective coding for Clean's natural-valued memory model. Keep limbs separate
    until their bounds are proved; combining unbounded limbs as a word loses data. -/
def pairCode {p : Nat} (w : Nat → ZMod p) (columns : Vector Nat 2) : Nat :=
  Nat.pair (w columns[0]).val (w columns[1]).val

@[simp] theorem WordColumns.code_u16 {p : Nat} (columns : Vector Nat 2) (w : Nat → ZMod p) :
    (WordColumns.u16 columns).code w = pairCode w columns := rfl

def MemoryAddress.code {p : Nat} (address : MemoryAddress) (w : Nat → ZMod p) : Nat :=
  match address with
  | .constantRegister index => Nat.pair 0 (Nat.pair index 0)
  | .register column => Nat.pair 0 (Nat.pair (w column).val 0)
  | .mixed selector registerOnTrue columns =>
    let space := if registerOnTrue then 1 - w selector else w selector
    Nat.pair space.val (pairCode w columns)

def MemoryPort.readCode {p : Nat} (port : MemoryPort) (w : Nat → ZMod p) : Nat :=
  port.readValue.code w

def MemoryPort.writeCode {p : Nat} (port : MemoryPort) (w : Nat → ZMod p) : Nat :=
  (port.writeValue.getD port.readValue).code w

/-- The actual port projected into Clean's memory-access object. The timestamp
    is the row's initial clock plus the imported in-cycle offset. -/
def MemoryPort.event {p : Nat} (port : MemoryPort) (columns : TraceColumns)
    (w : Nat → ZMod p) : MemoryAccess :=
  ((decodeTimestamp w columns.initialTime).value + port.clock.offset,
    port.address.code w, port.readCode w, port.writeCode w)

end Airbender.Trace
