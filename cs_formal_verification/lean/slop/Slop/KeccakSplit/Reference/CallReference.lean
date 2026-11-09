module
public import Human.Circuits.KeccakSplit.Call

@[expose] public section

namespace Airbender.Keccak.Split.Call.Proofs
set_option warningAsError true

theorem slot_count_bound (kind : Kind) : slotCount kind ≤ 7 := by
  cases kind <;> decide

/-- No blessed call aliases two of its actual lane accesses. Padding slots
are excluded exactly as in the public reference's access list. -/
theorem distinct_slots : ∀ index : Fin 361,
    ((slots index).toList.take (slotCount (kindAt index.val))).Nodup := by
  decide +kernel

end Airbender.Keccak.Split.Call.Proofs
