import Airbender.Review.Trace.Values
import Airbender.Review.Sail

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

/-- Read the supplied initial Sail state using its own GPR and little-endian
    byte-memory semantics. Missing registers/bytes remain actual Sail failures. -/
def Cell.read (cell : Cell) (before : Reference.RiscV.Sail.State) :=
  match cell with
  | .register index =>
    Reference.Sail.run (SailRV32.Functions.rX_bits (.Regidx index)) before
  | .ram address =>
    (_root_.Sail.ArchSem.readBytes (ue := SailRV32.exception) 4 address.toNat).run before

def Cell.initialToken (cell : Cell) (value : BitVec 32) : MemoryToken p :=
  let word := Word.ofBitVec value
  ⟨cell.addressCode, (0, 0), Nat.pair word.lo word.hi⟩

/-- Construct native initialization cells directly from a public Sail state.
    This is partial: every declared cell must be readable in the actual runtime. -/
def initialImage (before : Reference.RiscV.Sail.State) (cells : List Cell) :
    Option (List (MemoryToken p)) :=
  cells.mapM fun cell =>
    match cell.read before with
    | .ok value _ => some (cell.initialToken value)
    | .error _ _ => none

/-- Bind the native initial PC to Sail; the initial timestamp is public input. -/
def initialState (before : Reference.RiscV.Sail.State) (timestamp : ZMod p × ZMod p) :
    Option (PCState.State p) :=
  match Reference.Sail.run (SailRV32.Functions.get_arch_pc ()) before with
  | .ok pc _ => some (PCState.boundary pc timestamp)
  | .error _ _ => none

end Airbender.Trace
