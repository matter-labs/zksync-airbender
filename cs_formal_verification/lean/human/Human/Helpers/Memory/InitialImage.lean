import Human.Helpers.Memory.Values
import Human.Helpers.Core.CircuitOutput

namespace Airbender.PCState

/-- Canonical limb interpretation of the native state's PC columns. -/
def State.word (state : State p) : Arithmetic.Word := ⟨state.pc.1.val, state.pc.2.val⟩

end Airbender.PCState

namespace Airbender.Trace
open Arithmetic

/-- Public address domain, independent of the circuit witness. RAM entries are
    byte addresses; alignment and platform-domain conditions are separate. -/
inductive Cell where
  | register (index : BitVec 5)
  | ram (address : BitVec 32)
  deriving DecidableEq

/-- Injective native address code for a public cell. Register and RAM
    spaces stay distinct, and RAM byte addresses retain both limbs. -/
def Cell.addressCode : Cell → Nat
  | .register index => Nat.pair 0 (Nat.pair index.toNat 0)
  | .ram address =>
    let word := Word.ofBitVec address
    Nat.pair 1 (Nat.pair word.lo word.hi)

/-- Canonical native address limbs: a register index or a RAM byte address. -/
def Cell.addressWord : Cell → Word
  | .register index => ⟨index.toNat, 0⟩
  | .ram address => Word.ofBitVec address

/-- The actual imported address columns, before interpreting their address space. -/
def MemoryAddress.word {p : Nat} (address : MemoryAddress) (w : Nat → ZMod p) : Word :=
  match address with
  | .constantRegister index => ⟨index, 0⟩
  | .register column => ⟨(w column).val, 0⟩
  | .mixed _ _ columns => ⟨(w columns[0]).val, (w columns[1]).val⟩
  | .indirect port => ⟨(port.rawAddress w).1.val, (port.rawAddress w).2.val⟩

/-- RAM cells start at four-byte-aligned addresses; register cells need no alignment. -/
def Cell.Aligned : Cell → Prop
  | .register _ => True
  | .ram address => address.toNat % 4 = 0

/-- Encode a public cell value with prior timestamp zero. `value` is an
    actual 32-bit word; `initialImage` obtains it by reading Sail state. -/
def Cell.initialToken (cell : Cell) (value : BitVec 32) : MemoryToken p :=
  let word := Word.ofBitVec value
  ⟨cell.addressCode, (0, 0), Nat.pair word.lo word.hi⟩

end Airbender.Trace
