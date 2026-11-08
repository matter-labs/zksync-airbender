module
public import Slop.KeccakSplit.Reference.PhysicalSnapshot

@[expose] public section

namespace Airbender.Keccak.Split.Call.Proofs
open Trace Trace.Proofs
set_option warningAsError true

/-- The padding slot is never a live slot of a call. -/
theorem padding_not_live (index : Fin 361) :
    ¬ (slots index).toList.idxOf (30 : Fin 31) < slotCount (kindAt index.val) := by
  intro live
  have bound : (slots index).toList.idxOf (30 : Fin 31) < 7 :=
    lt_of_lt_of_le live (slot_count_bound _)
  have found : (slots index)[(slots index).toList.idxOf (30 : Fin 31)] = (30 : Fin 31) := by
    simpa only [Vector.getElem_toList] using List.getElem_idxOf
      (show (slots index).toList.idxOf (30 : Fin 31) < (slots index).toList.length by simpa using bound)
  have small := active_slot_bound index ⟨_, bound⟩ live
  simp only [Fin.getElem_fin, found] at small
  exact absurd small (by decide)

end Airbender.Keccak.Split.Call.Proofs
