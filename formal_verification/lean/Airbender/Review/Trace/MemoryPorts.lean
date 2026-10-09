import Airbender.Review.Trace.Columns
import Mathlib.Data.Nat.Pairing
import Clean.Utils.OfflineMemory

namespace Airbender.Trace

/-- Describe where a native port obtains its address. A register can be fixed
    or read from a variable; a mixed port uses two address limbs and a selector
    to choose register versus RAM. `registerOnTrue` records Rust's selector
    polarity. Actual selector values and address bounds come from the circuit/history. -/
inductive MemoryAddress where
  | constantRegister (index : Nat)
  | register (column : Nat)
  | mixed (selector : Nat) (registerOnTrue : Bool) (columns : Vector Nat 2)
  deriving DecidableEq

/-- Describe the variables holding a native word: constant zero, two limbs
    or four bytes. `evaluate` packs them with field arithmetic. This metadata
    identifies columns; it does not establish that their values have those ranges. -/
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

/-- One imported register/RAM access: its address, previous timestamp,
    read-value columns and optional write-value columns. `writeValue = none`
    preserves the read value while refreshing its timestamp. This describes
    the access; accepted initialized history proves what value it must read. -/
structure MemoryPort where
  /-- Previous-write clock columns and this access's native in-cycle offset. -/
  clock : TimestampPort
  /-- Register/RAM address interpretation imported for this port. -/
  address : MemoryAddress
  /-- Columns holding the value read from the preceding token. -/
  readValue : WordColumns
  /-- Columns holding the new value, or `none` for a readonly refresh. -/
  writeValue : Option WordColumns
  deriving DecidableEq

/-- Injective coding for Clean's natural-valued memory model. Keep limbs separate
    until their bounds are proved; combining unbounded limbs as a word loses data. -/
def pairCode {p : Nat} (w : Nat → ZMod p) (columns : Vector Nat 2) : Nat :=
  Nat.pair (w columns[0]).val (w columns[1]).val

@[simp] theorem WordColumns.code_u16 {p : Nat} (columns : Vector Nat 2) (w : Nat → ZMod p) :
    (WordColumns.u16 columns).code w = pairCode w columns := rfl

/-- Encode address space and raw limbs injectively for Clean's memory model.
    Space zero means register; space one means RAM. Bounds/Boolean selectors
    are proved separately, so this encoding does not silently truncate them. -/
def MemoryAddress.code {p : Nat} (address : MemoryAddress) (w : Nat → ZMod p) : Nat :=
  match address with
  | .constantRegister index => Nat.pair 0 (Nat.pair index 0)
  | .register column => Nat.pair 0 (Nat.pair (w column).val 0)
  | .mixed selector registerOnTrue columns =>
    let space := if registerOnTrue then 1 - w selector else w selector
    Nat.pair space.val (pairCode w columns)

def MemoryPort.readCode {p : Nat} (port : MemoryPort) (w : Nat → ZMod p) : Nat :=
  port.readValue.code w

/-- Use the imported write columns, or the read columns for a readonly port.
    This is the exact value passed to logical memory matching. -/
def MemoryPort.writeCode {p : Nat} (port : MemoryPort) (w : Nat → ZMod p) : Nat :=
  (port.writeValue.getD port.readValue).code w

/-- The actual port projected into Clean's memory-access object. The timestamp
    is the row's initial clock plus the imported in-cycle offset. -/
def MemoryPort.event {p : Nat} (port : MemoryPort) (columns : TraceColumns)
    (w : Nat → ZMod p) : MemoryAccess :=
  ((decodeTimestamp w columns.initialTime).value + port.clock.offset,
    port.address.code w, port.readCode w, port.writeCode w)

end Airbender.Trace
