import Airbender.Proofs.Trace.InitialImage
import Airbender.Proofs.Trace.MemoryOrigins

namespace Airbender.Trace.Proofs
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

theorem initialized_cells {p : Nat} [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1) {trace : Data p}
    (accepted : Accepted trace) (boundary : ClockBoundary trace)
    {before : Reference.RiscV.Sail.State} {cells : List Cell}
    (image : initialImage before cells = some trace.initialMemory) :
    ∀ row ∈ trace.rows, ∀ port ∈ row.ports,
      ∃ cell ∈ cells, port.address.code row.assignment = cell.addressCode := by
  intro row member port present
  have origin := initialized_addresses hp inverse accepted boundary row member port present
  rw [image_addresses image] at origin
  obtain ⟨cell, belongs, equal⟩ := List.mem_map.mp origin
  exact ⟨cell, belongs, equal.symm⟩

theorem address_bounds {p : Nat} [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1) {trace : Data p}
    (accepted : Accepted trace) (boundary : ClockBoundary trace)
    {before : Reference.RiscV.Sail.State} {cells : List Cell}
    (image : initialImage before cells = some trace.initialMemory) :
    ∀ row ∈ trace.rows, ∀ port ∈ row.ports, (port.address.word row.assignment).Bounded := by
  intro row member port present
  obtain ⟨cell, _, equal⟩ := initialized_cells hp inverse accepted boundary image row member port present
  rw [address_word equal]
  exact cell_address_bound cell

end Airbender.Trace.Proofs
