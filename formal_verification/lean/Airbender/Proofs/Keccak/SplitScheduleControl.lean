import Airbender.Review.Trace.Workers.Keccak.SplitSchedule

namespace Airbender.Keccak.Split.Proofs
set_option warningAsError true
set_option maxRecDepth 16384

/-- Recover a blessed call index from its public control encoding. -/
def indexOfControl (control : Nat) : Nat :=
  15 * (control / 64) + control / 8 % 8 +
    (if control % 8 = 0 then 0 else if control % 8 = 3 then 5 else 10)

/-- The decoder covers all calls, including the final delayed-iota call. -/
theorem index_of_control : ∀ index : Fin 361,
    indexOfControl (controlAt index.val) = index.val := by
  decide +kernel

/-- Two blessed calls cannot have the same full control word. -/
theorem control_injective {one two : Fin 361}
    (same : controlAt one.val = controlAt two.val) : one = two := by
  apply Fin.ext
  exact (index_of_control one).symm.trans
    ((congrArg indexOfControl same).trans (index_of_control two))

end Airbender.Keccak.Split.Proofs
