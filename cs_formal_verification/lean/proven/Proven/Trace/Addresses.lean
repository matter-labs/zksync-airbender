module
public import Proven.Trace.InitialImage
public import Proven.Trace.MemoryOrigins

@[expose] public section

namespace Airbender.Trace.Proofs

variable {Kind : Type} [CircuitLayout Kind]
open Arithmetic

theorem cell_address_bound (cell : Cell) : cell.addressWord.Bounded := by
  cases cell with
  | register index =>
    change index.toNat < limbBase ∧ 0 < limbBase
    exact ⟨lt_trans index.isLt (by decide : 32 < limbBase), by decide⟩
  | ram address => exact Word.ofBitVec_bound address

/-- Injective native coding preserves the limbs, including the high zero of a
    register address. No address-word bound is assumed in this projection. -/
theorem address_word {p : Nat} {address : MemoryAddress} {w : Nat → ZMod p} {cell : Cell}
    (same : address.code w = cell.addressCode) : address.word w = cell.addressWord := by
  cases address <;> cases cell
  all_goals simp only [MemoryAddress.code, Cell.addressCode, pairCode, Nat.pair_eq_pair] at same
  all_goals first
    | exact congrArg₂ Word.mk same.2.1 same.2.2
    | exact congrArg₂ Word.mk same.2.1 rfl

end Airbender.Trace.Proofs
