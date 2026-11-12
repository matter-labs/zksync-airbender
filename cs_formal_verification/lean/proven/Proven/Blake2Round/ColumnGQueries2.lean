module
public import Proven.Blake2Round.ColumnG

@[expose] public section

set_option warningAsError true

namespace Airbender.Blake2Round.Proofs

/-- The sixteen table rows and the carry flags of column G call 2. -/
theorem column_rows_2 {p : Nat} [Fact p.Prime] (hp : 262144 ≤ p)
    (compatible : 64 * (-31457280 : ZMod p) = 1) {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints setupTable)) :
    (columnTrace 2 w).Rows := by
  have hp512 : 512 ≤ p := by omega
  have field := Blake2G.Proofs.serialized_field compatible
  subst field
  unfold babyBearModulus at *
  refine
    { q0 := query_55 hp512 h (importedConstraints.lookup_34 _ (query_lt (by decide))) ?_ ?_ ?_ ?_
      ka0 := carry_55 hp512 h (importedConstraints.lookup_34 _ (query_lt (by decide))) ?_ ?_
      q1 := query_4 hp512 h (importedConstraints.lookup_35 _ (query_lt (by decide))) ?_ ?_ ?_ ?_
      q2 := query_55 hp512 h (importedConstraints.lookup_36 _ (query_lt (by decide))) ?_ ?_ ?_ ?_
      ka1 := carry_55 hp512 h (importedConstraints.lookup_36 _ (query_lt (by decide))) ?_ ?_
      q3 := query_4 hp512 h (importedConstraints.lookup_37 _ (query_lt (by decide))) ?_ ?_ ?_ ?_
      q4 := query_20 hp512 h (importedConstraints.lookup_38 _ (query_lt (by decide))) ?_ ?_ ?_ ?_
      q5 := query_20 hp512 h (importedConstraints.lookup_39 _ (query_lt (by decide))) ?_ ?_ ?_ ?_
      q6 := query_57 hp512 h (importedConstraints.lookup_40 _ (query_lt (by decide)))
        ?_ ?_ ?_ ?_ ?_ ?_
      q7 := query_57 hp512 h (importedConstraints.lookup_41 _ (query_lt (by decide)))
        ?_ ?_ ?_ ?_ ?_ ?_
      q8 := query_4 hp512 h (importedConstraints.lookup_42 _ (query_lt (by decide))) ?_ ?_ ?_ ?_
      q9 := query_4 hp512 h (importedConstraints.lookup_43 _ (query_lt (by decide))) ?_ ?_ ?_ ?_
      q10 := query_55 hp512 h (importedConstraints.lookup_44 _ (query_lt (by decide))) ?_ ?_ ?_ ?_
      kb0 := carry_55 hp512 h (importedConstraints.lookup_44 _ (query_lt (by decide))) ?_ ?_
      q11 := query_55 hp512 h (importedConstraints.lookup_45 _ (query_lt (by decide))) ?_ ?_ ?_ ?_
      kb1 := carry_55 hp512 h (importedConstraints.lookup_45 _ (query_lt (by decide))) ?_ ?_
      q12 := query_20 hp512 h (importedConstraints.lookup_46 _ (query_lt (by decide))) ?_ ?_ ?_ ?_
      q13 := query_20 hp512 h (importedConstraints.lookup_47 _ (query_lt (by decide))) ?_ ?_ ?_ ?_
      q14 := query_19 hp512 h (importedConstraints.lookup_48 _ (query_lt (by decide))) ?_ ?_ ?_ ?_
      q15 := query_19 hp512 h (importedConstraints.lookup_49 _ (query_lt (by decide))) ?_ ?_ ?_ ?_
      kc0 := flag_carry h (importedConstraints.constraint_145 _ (constraint_lt (by decide))) ?_
      kc1 := flag_carry h (importedConstraints.constraint_146 _ (constraint_lt (by decide))) ?_
      kd0 := flag_carry h (importedConstraints.constraint_147 _ (constraint_lt (by decide))) ?_
      kd1 := flag_carry h (importedConstraints.constraint_148 _ (constraint_lt (by decide))) ?_ }
  all_goals column_eq

end Airbender.Blake2Round.Proofs
