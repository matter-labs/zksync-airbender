import Human.Helpers.Memory.Native
import Human.Helpers.Memory.InitialImageRV
import Human.ISA.RV32

/-! The shared conclusion of trace-level claims over our RV32 spec: an accepted trace is a run of `RV.run` from the
    public starting state `initial : RV.State` (not a Sail execution). RV sibling of `Execution.lean`'s `Realizes`. -/

namespace Airbender.Trace
open Arithmetic

/-- RV sibling of `InitialProfile` (`Helpers/Memory/Initialization.lean`): PC 0, all registers 0, tracked RAM outside
    ROM 0. ROM keeps the public program bytes. -/
structure RVInitialProfile (initial : RV.State) (cells : List Cell) : Prop where
  pc : initial.pc = 0
  registers : ∀ index, (Cell.register index).readRV initial = some 0
  ram : ∀ address, Cell.ram address ∈ cells → ROM.limit ≤ address.toNat →
    (Cell.ram address).readRV initial = some 0

namespace ROMView

/-- RV sibling of `publicWord`: the ROM word of the public starting state. -/
def publicWordRV (initial : RV.State) (address : Nat) : Word :=
  let limbs := Nat.unpair (Nat.unpair address).2
  match (Cell.ram (Word.mk limbs.1 limbs.2).toBitVec).readRV initial with
  | some value => Word.ofBitVec value
  | none => ⟨0, 0⟩

/-- RV sibling of `token`: ROM shadow slots read the public bytes; other tokens are unchanged. -/
def tokenRV {p : Nat} (initial : RV.State) (native : MemoryToken p) : MemoryToken p :=
  if shadow native.address then
    { native with value := (Nat.pair (publicWordRV initial native.address).lo
      (publicWordRV initial native.address).hi) }
  else native

end ROMView

/-- An accepted trace is a run of our spec: some number of `RV.step`s from `initial` reach a state whose PC and
    tracked cells are the trace's terminal ones (`view` reinterprets native ROM shadow tokens as the public bytes).
    This definition adds no assumptions. -/
def RVRealizes {Kind : Type} [CircuitLayout Kind] {p : Nat} [Fact p.Prime] (trace : Data p Kind)
    (initial : RV.State) (cells : List Cell) (view : MemoryToken p → MemoryToken p := id) : Prop :=
  ∃ n after, RV.run n initial = some after ∧ after.pc = trace.terminal.word.toBitVec ∧
    ∀ sink ∈ trace.terminalMemory, ∃ cell ∈ cells, cell.addressCode = sink.address ∧
      cell.readRV after = some (view sink).word.toBitVec

end Airbender.Trace
