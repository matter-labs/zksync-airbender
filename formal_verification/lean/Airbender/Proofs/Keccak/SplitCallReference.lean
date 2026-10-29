import Airbender.Review.Circuits.Keccak.SplitCall

namespace Airbender.Keccak.Split.Call.Proofs
set_option warningAsError true

theorem slot_count_bound (kind : Kind) : slotCount kind ≤ 7 := by
  cases kind <;> decide

/-- No blessed call aliases two of its actual lane accesses. Padding slots
are excluded exactly as in the public reference's access list. -/
theorem distinct_slots : ∀ index : Fin 361,
    ((slots index).toList.take (slotCount (kindAt index.val))).Nodup := by
  decide +kernel

/-- Pi's physical renaming returns to the original lane placement after the
twenty-four rounds. This is about the public schedule, not native acceptance. -/
theorem final_slot_map : ∀ lane : Fin 25, physicalSlot 24 lane = lane := by
  decide +kernel

end Airbender.Keccak.Split.Call.Proofs
