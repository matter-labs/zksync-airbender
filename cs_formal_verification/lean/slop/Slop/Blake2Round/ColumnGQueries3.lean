module
public import Slop.Blake2Round.ColumnG

@[expose] public section

set_option warningAsError true

namespace Airbender.Blake2Round.Proofs

/-- The sixteen table rows and the carry flags of column G call 3. -/
theorem column_rows_3 {p : Nat} [Fact p.Prime] (hp : 262144 ≤ p)
    (compatible : 64 * (-31457280 : ZMod p) = 1) {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints setupTable)) :
    (columnTrace 3 w).Rows := by
  have hp512 : 512 ≤ p := by omega
  have field := Blake2G.Proofs.serialized_field compatible
  subst field
  unfold babyBearModulus at *
  refine
    { q0 := query_55 hp512 h (importedConstraints.lookup_50 _ (query_lt (by decide))) ?_ ?_ ?_ ?_
      ka0 := carry_55 hp512 h (importedConstraints.lookup_50 _ (query_lt (by decide))) ?_ ?_
      q1 := query_4 hp512 h (importedConstraints.lookup_51 _ (query_lt (by decide))) ?_ ?_ ?_ ?_
      q2 := query_55 hp512 h (importedConstraints.lookup_52 _ (query_lt (by decide))) ?_ ?_ ?_ ?_
      ka1 := carry_55 hp512 h (importedConstraints.lookup_52 _ (query_lt (by decide))) ?_ ?_
      q3 := query_4 hp512 h (importedConstraints.lookup_53 _ (query_lt (by decide))) ?_ ?_ ?_ ?_
      q4 := query_20 hp512 h (importedConstraints.lookup_54 _ (query_lt (by decide))) ?_ ?_ ?_ ?_
      q5 := query_20 hp512 h (importedConstraints.lookup_55 _ (query_lt (by decide))) ?_ ?_ ?_ ?_
      q6 := query_57 hp512 h (importedConstraints.lookup_56 _ (query_lt (by decide)))
        ?_ ?_ ?_ ?_ ?_ ?_
      q7 := query_57 hp512 h (importedConstraints.lookup_57 _ (query_lt (by decide)))
        ?_ ?_ ?_ ?_ ?_ ?_
      q8 := query_4 hp512 h (importedConstraints.lookup_58 _ (query_lt (by decide))) ?_ ?_ ?_ ?_
      q9 := query_4 hp512 h (importedConstraints.lookup_59 _ (query_lt (by decide))) ?_ ?_ ?_ ?_
      q10 := query_55 hp512 h (importedConstraints.lookup_60 _ (query_lt (by decide))) ?_ ?_ ?_ ?_
      kb0 := carry_55 hp512 h (importedConstraints.lookup_60 _ (query_lt (by decide))) ?_ ?_
      q11 := query_55 hp512 h (importedConstraints.lookup_61 _ (query_lt (by decide))) ?_ ?_ ?_ ?_
      kb1 := carry_55 hp512 h (importedConstraints.lookup_61 _ (query_lt (by decide))) ?_ ?_
      q12 := query_20 hp512 h (importedConstraints.lookup_62 _ (query_lt (by decide))) ?_ ?_ ?_ ?_
      q13 := query_20 hp512 h (importedConstraints.lookup_63 _ (query_lt (by decide))) ?_ ?_ ?_ ?_
      q14 := query_19 hp512 h (importedConstraints.lookup_64 _ (query_lt (by decide))) ?_ ?_ ?_ ?_
      q15 := query_19 hp512 h (importedConstraints.lookup_65 _ (query_lt (by decide))) ?_ ?_ ?_ ?_
      kc0 := flag_carry h (importedConstraints.constraint_149 _ (constraint_lt (by decide))) ?_
      kc1 := flag_carry h (importedConstraints.constraint_150 _ (constraint_lt (by decide))) ?_
      kd0 := flag_carry h (importedConstraints.constraint_151 _ (constraint_lt (by decide))) ?_
      kd1 := flag_carry h (importedConstraints.constraint_152 _ (constraint_lt (by decide))) ?_ }
  all_goals column_eq

end Airbender.Blake2Round.Proofs
