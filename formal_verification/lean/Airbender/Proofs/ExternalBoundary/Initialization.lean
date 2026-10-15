import Airbender.Review.Helpers.Context.ExternalBoundary.Initialization
import Airbender.Proofs.Trace.InitialImage

namespace Airbender.ExternalBoundary.Initialization.Proofs
open Trace
set_option warningAsError true

theorem address_bound (position : Position geometry) : address position < 2 ^ 32 := by
  have a := position.1.isLt
  have b := position.2.isLt
  have positive := geometry.positive
  have extent := geometry.extent
  dsimp [address]
  nlinarith

theorem address_injective : Function.Injective (address (geometry := geometry)) := by
  intro a b equal
  have raw : a.1.val * geometry.words + a.2.val = b.1.val * geometry.words + b.2.val := by
    dsimp [address] at equal
    omega
  have offsets := congrArg (fun n => n % geometry.words) raw
  simp only [Nat.add_mod, Nat.mul_mod_left, zero_add,
    Nat.mod_eq_of_lt a.2.isLt, Nat.mod_eq_of_lt b.2.isLt] at offsets
  have second : a.2 = b.2 := Fin.ext offsets
  have first : a.1 = b.1 := by
    apply Fin.ext
    apply Nat.mul_right_cancel geometry.positive
    simpa only [offsets, Nat.add_left_inj] using raw
  exact Prod.ext first second

theorem cell_injective : Function.Injective (cell (geometry := geometry)) := by
  intro a b same
  have raw := congrArg (fun c => match c with | Cell.ram address => address.toNat | _ => 0) same
  simp only [cell, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (address_bound a),
    Nat.mod_eq_of_lt (address_bound b)] at raw
  exact address_injective raw

theorem registers_distinct : registers.Nodup := by decide

theorem cells_distinct (selection : Selection geometry) : (cells selection).Nodup := by
  apply registers_distinct.append
    ((selection.unique.product (List.nodup_finRange _)).map cell_injective)
  intro c register ram
  obtain ⟨i, _, equal⟩ := List.mem_map.mp register
  obtain ⟨j, _, equal'⟩ := List.mem_map.mp ram
  cases equal.trans equal'.symm

theorem addresses_distinct (selection : Selection geometry) :
    ((cells selection).map Cell.addressCode).Nodup :=
  (cells_distinct selection).map Trace.Proofs.cell_address_injective

theorem aligned (selection : Selection geometry) : ∀ c ∈ cells selection, c.Aligned := by
  intro c member
  rcases List.mem_append.mp member with register | ram
  · obtain ⟨i, _, rfl⟩ := List.mem_map.mp register
    trivial
  · obtain ⟨position, _, rfl⟩ := List.mem_map.mp ram
    change (address position % 2 ^ 32) % 4 = 0
    rw [Nat.mod_eq_of_lt (address_bound position)]
    exact Nat.mul_mod_right _ _

theorem all_registers (selection : Selection geometry) (index : BitVec 5) :
    Cell.register index ∈ cells selection := by
  apply List.mem_append_left
  refine List.mem_map.mpr ⟨⟨index.toNat, index.isLt⟩, List.mem_finRange _, ?_⟩
  simp

end Airbender.ExternalBoundary.Initialization.Proofs
