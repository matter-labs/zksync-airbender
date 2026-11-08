module
public import Slop.Blake2Round.DiagonalG

@[expose] public section

set_option warningAsError true

namespace Airbender.Blake2Round.Proofs

/-- The sixteen table rows and the carry flags of diagonal G call 3. -/
theorem diagonal_rows_3 {p : Nat} [Fact p.Prime] (hp : 262144 ≤ p)
    (compatible : 64 * (-31457280 : ZMod p) = 1) {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints setupTable)) :
    (diagonalTrace 3 w).Rows := by
  have hp512 : 512 ≤ p := by omega
  have field := Blake2G.Proofs.serialized_field compatible
  subst field
  unfold babyBearModulus at *
  refine
    { q0 := query_55 hp512 h (importedConstraints.lookup_114 _ (query_lt (by decide))) ?_ ?_ ?_ ?_
      ka0 := carry_55 hp512 h (importedConstraints.lookup_114 _ (query_lt (by decide))) ?_ ?_
      q1 := query_4 hp512 h (importedConstraints.lookup_115 _ (query_lt (by decide))) ?_ ?_ ?_ ?_
      q2 := query_55 hp512 h (importedConstraints.lookup_116 _ (query_lt (by decide))) ?_ ?_ ?_ ?_
      ka1 := carry_55 hp512 h (importedConstraints.lookup_116 _ (query_lt (by decide))) ?_ ?_
      q3 := query_4 hp512 h (importedConstraints.lookup_117 _ (query_lt (by decide))) ?_ ?_ ?_ ?_
      q4 := query_20 hp512 h (importedConstraints.lookup_118 _ (query_lt (by decide))) ?_ ?_ ?_ ?_
      q5 := query_20 hp512 h (importedConstraints.lookup_119 _ (query_lt (by decide))) ?_ ?_ ?_ ?_
      q6 := query_57 hp512 h (importedConstraints.lookup_120 _ (query_lt (by decide)))
        ?_ ?_ ?_ ?_ ?_ ?_
      q7 := query_57 hp512 h (importedConstraints.lookup_121 _ (query_lt (by decide)))
        ?_ ?_ ?_ ?_ ?_ ?_
      q8 := query_4 hp512 h (importedConstraints.lookup_122 _ (query_lt (by decide))) ?_ ?_ ?_ ?_
      q9 := query_4 hp512 h (importedConstraints.lookup_123 _ (query_lt (by decide))) ?_ ?_ ?_ ?_
      q10 := query_55 hp512 h (importedConstraints.lookup_124 _ (query_lt (by decide))) ?_ ?_ ?_ ?_
      kb0 := carry_55 hp512 h (importedConstraints.lookup_124 _ (query_lt (by decide))) ?_ ?_
      q11 := query_55 hp512 h (importedConstraints.lookup_125 _ (query_lt (by decide))) ?_ ?_ ?_ ?_
      kb1 := carry_55 hp512 h (importedConstraints.lookup_125 _ (query_lt (by decide))) ?_ ?_
      q12 := query_20 hp512 h (importedConstraints.lookup_126 _ (query_lt (by decide))) ?_ ?_ ?_ ?_
      q13 := query_20 hp512 h (importedConstraints.lookup_127 _ (query_lt (by decide))) ?_ ?_ ?_ ?_
      q14 := query_56 hp512 h (importedConstraints.lookup_128 _ (query_lt (by decide))) ?_ ?_ ?_ ?_
      kd0 := carry_56 hp512 h (importedConstraints.lookup_128 _ (query_lt (by decide))) ?_ ?_
      q15 := query_56 hp512 h (importedConstraints.lookup_129 _ (query_lt (by decide))) ?_ ?_ ?_ ?_
      kd1 := carry_56 hp512 h (importedConstraints.lookup_129 _ (query_lt (by decide))) ?_ ?_
      kc0 := flag_carry h (importedConstraints.constraint_159 _ (constraint_lt (by decide))) ?_
      kc1 := flag_carry h (importedConstraints.constraint_160 _ (constraint_lt (by decide))) ?_ }
  all_goals diagonal_eq

end Airbender.Blake2Round.Proofs
