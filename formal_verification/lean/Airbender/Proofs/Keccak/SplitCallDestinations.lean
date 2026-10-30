import Airbender.Proofs.Trace.SailCells
import Airbender.Proofs.Keccak.SplitCallReference

namespace Airbender.Keccak.Split.Call.Proofs
open Trace Trace.Proofs Reference.RiscV.Sail
set_option warningAsError true
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
set_option Elab.async false

/-- An aligned blessed pointer leaves room for every complete physical lane. -/
theorem lane_address_value (pointer : BitVec 32) (aligned : pointer.toNat % 256 = 0)
    (slot : Fin 31) (high : Bool) :
    (pointer + BitVec.ofNat 32 (8 * slot.val + if high then 4 else 0)).toNat =
      pointer.toNat + 8 * slot.val + if high then 4 else 0 := by
  have room : pointer.toNat + 8 * slot.val + (if high then 4 else 0) < 2 ^ 32 := by
    have pointerBound := pointer.isLt
    have slotBound := slot.isLt
    cases high <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega
  have offset : 8 * slot.val + (if high then 4 else 0) < 2 ^ 32 := by omega
  have total : pointer.toNat + (8 * slot.val + if high then 4 else 0) < 2 ^ 32 := by omega
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt offset, Nat.mod_eq_of_lt total]
  omega

/-- Different physical lane halves have different Sail cells. -/
theorem lane_cell_injective (pointer : BitVec 32) (aligned : pointer.toNat % 256 = 0) :
    Function.Injective (fun location : Fin 31 × Bool => laneCell pointer location.1 location.2) := by
  rintro ⟨one, first⟩ ⟨two, second⟩ same
  have address := Cell.ram.inj same
  have numeric := congrArg BitVec.toNat address
  rw [lane_address_value pointer aligned, lane_address_value pointer aligned] at numeric
  cases first <;> cases second <;> simp only [Bool.false_eq_true, ↓reduceIte] at numeric
  all_goals first
    | (have equal : one.val = two.val := by omega
       exact Prod.ext (Fin.ext equal) rfl)
    | omega

/-- Every physical lane half is word aligned. -/
theorem lane_cell_aligned (pointer : BitVec 32) (aligned : pointer.toNat % 256 = 0)
    (slot : Fin 31) (high : Bool) : (laneCell pointer slot high).Aligned := by
  change (pointer + BitVec.ofNat 32 (8 * slot.val + if high then 4 else 0)).toNat % 4 = 0
  rw [lane_address_value pointer aligned]
  cases high <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega

private abbrev Destination := Sum (Fin 2) (Fin 31 × Bool)

private def destinationCell (pointer : BitVec 32) : Destination → Cell
  | .inl register => .register (BitVec.ofNat 5 (10 + register.val))
  | .inr location => laneCell pointer location.1 location.2

private theorem destination_cell_injective (pointer : BitVec 32) (aligned : pointer.toNat % 256 = 0) :
    Function.Injective (destinationCell pointer) := by
  intro one two same
  cases one with
  | inl first =>
    cases two with
    | inl second =>
      fin_cases first <;> fin_cases second <;> simp_all [destinationCell]
    | inr second => cases same
  | inr first =>
    cases two with
    | inl second => cases same
    | inr second =>
      exact congrArg Sum.inr (lane_cell_injective pointer aligned same)

private def destinations (index : Fin 361) : List Destination :=
  [.inl 0, .inl 1] ++ ((slots index).toList.take (slotCount (kindAt index.val))).flatMap fun physical =>
    [.inr (physical, false), .inr (physical, true)]

private theorem doubled_nodup {α : Type} {values : List α} (distinct : values.Nodup) :
    (values.flatMap fun value => [(value, false), (value, true)]).Nodup := by
  induction values with
  | nil => simp
  | cons value rest ih =>
    have facts := List.nodup_cons.mp distinct
    have missing (high : Bool) : (value, high) ∉ rest.flatMap (fun other => [(other, false), (other, true)]) := by
      intro member
      obtain ⟨other, present, pair⟩ := List.mem_flatMap.mp member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at pair
      rcases pair with same | same
      all_goals
        have first : value = other := congrArg Prod.fst same
        apply facts.1
        rw [first]
        exact present
    simp only [List.flatMap_cons, List.cons_append, List.nil_append, List.nodup_cons]
    exact ⟨by simp only [List.mem_cons, not_or]; exact ⟨by simp, missing false⟩,
      missing true, ih facts.2⟩

private theorem destinations_nodup (index : Fin 361) : (destinations index).Nodup := by
  let ram := ((slots index).toList.take (slotCount (kindAt index.val))).flatMap fun physical =>
    [(physical, false), (physical, true)]
  have memory : (ram.map (Sum.inr : Fin 31 × Bool → Destination)).Nodup :=
    (doubled_nodup (distinct_slots index)).map Sum.inr_injective
  have absent (register : Fin 2) : Sum.inl register ∉ ram.map (Sum.inr : Fin 31 × Bool → Destination) := by simp
  have equation : destinations index = [Sum.inl (0 : Fin 2), Sum.inl 1] ++ ram.map Sum.inr := by
    simp only [destinations, ram, List.map_flatMap, List.map_cons, List.map_nil]
  rw [equation]
  simp only [List.cons_append, List.nil_append, List.nodup_cons]
  exact ⟨by simp only [List.mem_cons, not_or]; exact ⟨by decide, absent 0⟩, absent 1, memory⟩

private theorem taken_slots (index : Fin 361) :
    (slots index).toList.take (slotCount (kindAt index.val)) =
      (List.range (slotCount (kindAt index.val))).map (fun lane => ((slots index)[lane]?).getD 0) := by
  apply List.ext_getElem
  · simp [Nat.min_eq_left (slot_count_bound _)]
  · intro lane first second
    have live : lane < slotCount (kindAt index.val) := by simpa using second
    have bound : lane < 7 := lt_of_lt_of_le live (slot_count_bound _)
    simp [bound]

private theorem write_address_codes (index : Fin 361) (pointer : BitVec 32) (output : Vector Nat 7) :
    (writes index pointer output).map (fun entry => entry.1.addressCode) =
      (destinations index).map (fun location => (destinationCell pointer location).addressCode) := by
  simp only [writes, destinations, List.map_append, List.map_cons, List.map_nil, List.map_flatMap]
  rw [taken_slots, List.flatMap_map]
  congr 1
  apply List.flatMap_congr
  intro lane member
  have bound : lane < 7 := lt_of_lt_of_le (List.mem_range.mp member) (slot_count_bound _)
  simp only [bound, ↓reduceDIte, List.map_cons, List.map_nil, destinationCell]
  simp [bound]

/-- All actual declared write addresses are distinct. -/
theorem writes_distinct (index : Fin 361) (pointer : BitVec 32)
    (aligned : pointer.toNat % 256 = 0) (output : Vector Nat 7) :
    ((writes index pointer output).map (fun entry => entry.1.addressCode)).Nodup := by
  rw [write_address_codes]
  apply (destinations_nodup index).map
  intro one two same
  exact destination_cell_injective pointer aligned (cell_address_injective same)

/-- Every declared write uses an aligned register or lane cell. -/
theorem writes_aligned (index : Fin 361) (pointer : BitVec 32)
    (aligned : pointer.toNat % 256 = 0) (output : Vector Nat 7) :
    ∀ entry ∈ writes index pointer output, entry.1.Aligned := by
  intro entry member
  rcases List.mem_append.mp member with register | memory
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at register
    rcases register with rfl | rfl <;> trivial
  · obtain ⟨lane, _, present⟩ := List.mem_flatMap.mp memory
    split_ifs at present with valid
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at present
      rcases present with rfl | rfl <;> exact lane_cell_aligned pointer aligned _ _
    · cases present

end Airbender.Keccak.Split.Call.Proofs
