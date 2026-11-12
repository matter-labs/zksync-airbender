module
public import Proven.Blake2Round.ColumnG

@[expose] public section

set_option warningAsError true

namespace Airbender.Blake2Round.Proofs

/-- The sixteen table rows and the carry flags of column G call 0. -/
theorem column_rows_0 {p : Nat} [Fact p.Prime] (hp : 262144 ≤ p)
    (compatible : 64 * (-31457280 : ZMod p) = 1) {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints setupTable)) :
    (columnTrace 0 w).Rows := by
  have hp512 : 512 ≤ p := by omega
  have field := Blake2G.Proofs.serialized_field compatible
  subst field
  unfold babyBearModulus at *
  refine
    { q0 := query_55 hp512 h (importedConstraints.lookup_2 _ (query_lt (by decide))) ?_ ?_ ?_ ?_
      ka0 := carry_55 hp512 h (importedConstraints.lookup_2 _ (query_lt (by decide))) ?_ ?_
      q1 := query_4 hp512 h (importedConstraints.lookup_3 _ (query_lt (by decide))) ?_ ?_ ?_ ?_
      q2 := query_55 hp512 h (importedConstraints.lookup_4 _ (query_lt (by decide))) ?_ ?_ ?_ ?_
      ka1 := carry_55 hp512 h (importedConstraints.lookup_4 _ (query_lt (by decide))) ?_ ?_
      q3 := query_4 hp512 h (importedConstraints.lookup_5 _ (query_lt (by decide))) ?_ ?_ ?_ ?_
      q4 := query_20 hp512 h (importedConstraints.lookup_6 _ (query_lt (by decide))) ?_ ?_ ?_ ?_
      q5 := query_20 hp512 h (importedConstraints.lookup_7 _ (query_lt (by decide))) ?_ ?_ ?_ ?_
      q6 := query_57 hp512 h (importedConstraints.lookup_8 _ (query_lt (by decide)))
        ?_ ?_ ?_ ?_ ?_ ?_
      q7 := query_57 hp512 h (importedConstraints.lookup_9 _ (query_lt (by decide)))
        ?_ ?_ ?_ ?_ ?_ ?_
      q8 := query_4 hp512 h (importedConstraints.lookup_10 _ (query_lt (by decide))) ?_ ?_ ?_ ?_
      q9 := query_4 hp512 h (importedConstraints.lookup_11 _ (query_lt (by decide))) ?_ ?_ ?_ ?_
      q10 := query_55 hp512 h (importedConstraints.lookup_12 _ (query_lt (by decide))) ?_ ?_ ?_ ?_
      kb0 := carry_55 hp512 h (importedConstraints.lookup_12 _ (query_lt (by decide))) ?_ ?_
      q11 := query_55 hp512 h (importedConstraints.lookup_13 _ (query_lt (by decide))) ?_ ?_ ?_ ?_
      kb1 := carry_55 hp512 h (importedConstraints.lookup_13 _ (query_lt (by decide))) ?_ ?_
      q12 := query_20 hp512 h (importedConstraints.lookup_14 _ (query_lt (by decide))) ?_ ?_ ?_ ?_
      q13 := query_20 hp512 h (importedConstraints.lookup_15 _ (query_lt (by decide))) ?_ ?_ ?_ ?_
      q14 := query_19 hp512 h (importedConstraints.lookup_16 _ (query_lt (by decide))) ?_ ?_ ?_ ?_
      q15 := query_19 hp512 h (importedConstraints.lookup_17 _ (query_lt (by decide))) ?_ ?_ ?_ ?_
      kc0 := flag_carry h (importedConstraints.constraint_137 _ (constraint_lt (by decide))) ?_
      kc1 := flag_carry h (importedConstraints.constraint_138 _ (constraint_lt (by decide))) ?_
      kd0 := flag_carry h (importedConstraints.constraint_139 _ (constraint_lt (by decide))) ?_
      kd1 := flag_carry h (importedConstraints.constraint_140 _ (constraint_lt (by decide))) ?_ }
  all_goals column_eq

end Airbender.Blake2Round.Proofs
