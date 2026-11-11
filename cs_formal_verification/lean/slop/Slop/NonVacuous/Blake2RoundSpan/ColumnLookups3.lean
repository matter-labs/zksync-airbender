module
public import Slop.NonVacuous.Blake2RoundSpan.Queries
public import Slop.Blake2Round.ColumnG

@[expose] public section

/-! The sixteen fixed-table queries of column G call 3 (imported lookups 50 to 65) hold over BabyBear
    when its trace's table facts do (`Blake2Round.Proofs.GTrace.Rows`), for any assignment: one lemma per query,
    whose entries evaluate to the trace's fields (`column_eq`). -/

namespace Airbender.NonVacuous.Blake2RoundSpan
open Blake2Round.Proofs

variable {p : Nat} [Fact p.Prime] (hp : p = 2013265921) (w : Nat → ZMod p) (rows : (columnTrace 3 w).Rows)
include hp rows

private theorem column_lookup_50 {L : List (Lookup (ZMod p))}
    (hL : FlatOperation.lookups (Blake2Round.importedConstraints Blake2Round.setupTable) = L) {n : Nat}
    {hn : n < L.length} (index : n = 50) : (L.get ⟨n, hn⟩).Contains (Verification.environment w) := by
  subst hp
  refine contains_carry hL (Blake2Round.importedConstraints.lookup_50 _ (query_lt (by decide))) index (Or.inl ⟨rfl, rfl⟩) rows.q0 rows.ka0 ?_ ?_ ?_ ?_ ?_ ?_
  all_goals column_eq

private theorem column_lookup_51 {L : List (Lookup (ZMod p))}
    (hL : FlatOperation.lookups (Blake2Round.importedConstraints Blake2Round.setupTable) = L) {n : Nat}
    {hn : n < L.length} (index : n = 51) : (L.get ⟨n, hn⟩).Contains (Verification.environment w) := by
  subst hp
  refine contains_xor hL (Blake2Round.importedConstraints.lookup_51 _ (query_lt (by decide))) index (Or.inl ⟨rfl, rfl⟩) rows.q1 ?_ ?_ ?_ ?_ ?_ ?_
  all_goals column_eq

private theorem column_lookup_52 {L : List (Lookup (ZMod p))}
    (hL : FlatOperation.lookups (Blake2Round.importedConstraints Blake2Round.setupTable) = L) {n : Nat}
    {hn : n < L.length} (index : n = 52) : (L.get ⟨n, hn⟩).Contains (Verification.environment w) := by
  subst hp
  refine contains_carry hL (Blake2Round.importedConstraints.lookup_52 _ (query_lt (by decide))) index (Or.inl ⟨rfl, rfl⟩) rows.q2 rows.ka1 ?_ ?_ ?_ ?_ ?_ ?_
  all_goals column_eq

private theorem column_lookup_53 {L : List (Lookup (ZMod p))}
    (hL : FlatOperation.lookups (Blake2Round.importedConstraints Blake2Round.setupTable) = L) {n : Nat}
    {hn : n < L.length} (index : n = 53) : (L.get ⟨n, hn⟩).Contains (Verification.environment w) := by
  subst hp
  refine contains_xor hL (Blake2Round.importedConstraints.lookup_53 _ (query_lt (by decide))) index (Or.inl ⟨rfl, rfl⟩) rows.q3 ?_ ?_ ?_ ?_ ?_ ?_
  all_goals column_eq

private theorem column_lookup_54 {L : List (Lookup (ZMod p))}
    (hL : FlatOperation.lookups (Blake2Round.importedConstraints Blake2Round.setupTable) = L) {n : Nat}
    {hn : n < L.length} (index : n = 54) : (L.get ⟨n, hn⟩).Contains (Verification.environment w) := by
  subst hp
  refine contains_xor hL (Blake2Round.importedConstraints.lookup_54 _ (query_lt (by decide))) index (Or.inr (Or.inr ⟨rfl, rfl⟩)) rows.q4 ?_ ?_ ?_ ?_ ?_ ?_
  all_goals column_eq

private theorem column_lookup_55 {L : List (Lookup (ZMod p))}
    (hL : FlatOperation.lookups (Blake2Round.importedConstraints Blake2Round.setupTable) = L) {n : Nat}
    {hn : n < L.length} (index : n = 55) : (L.get ⟨n, hn⟩).Contains (Verification.environment w) := by
  subst hp
  refine contains_xor hL (Blake2Round.importedConstraints.lookup_55 _ (query_lt (by decide))) index (Or.inr (Or.inr ⟨rfl, rfl⟩)) rows.q5 ?_ ?_ ?_ ?_ ?_ ?_
  all_goals column_eq

private theorem column_lookup_56 {L : List (Lookup (ZMod p))}
    (hL : FlatOperation.lookups (Blake2Round.importedConstraints Blake2Round.setupTable) = L) {n : Nat}
    {hn : n < L.length} (index : n = 56) : (L.get ⟨n, hn⟩).Contains (Verification.environment w) := by
  subst hp
  refine contains_split hL (Blake2Round.importedConstraints.lookup_56 _ (query_lt (by decide))) index rows.q6 ?_ ?_ ?_ ?_ ?_ ?_
  all_goals column_eq

private theorem column_lookup_57 {L : List (Lookup (ZMod p))}
    (hL : FlatOperation.lookups (Blake2Round.importedConstraints Blake2Round.setupTable) = L) {n : Nat}
    {hn : n < L.length} (index : n = 57) : (L.get ⟨n, hn⟩).Contains (Verification.environment w) := by
  subst hp
  refine contains_split hL (Blake2Round.importedConstraints.lookup_57 _ (query_lt (by decide))) index rows.q7 ?_ ?_ ?_ ?_ ?_ ?_
  all_goals column_eq

private theorem column_lookup_58 {L : List (Lookup (ZMod p))}
    (hL : FlatOperation.lookups (Blake2Round.importedConstraints Blake2Round.setupTable) = L) {n : Nat}
    {hn : n < L.length} (index : n = 58) : (L.get ⟨n, hn⟩).Contains (Verification.environment w) := by
  subst hp
  refine contains_xor hL (Blake2Round.importedConstraints.lookup_58 _ (query_lt (by decide))) index (Or.inl ⟨rfl, rfl⟩) rows.q8 ?_ ?_ ?_ ?_ ?_ ?_
  all_goals column_eq

private theorem column_lookup_59 {L : List (Lookup (ZMod p))}
    (hL : FlatOperation.lookups (Blake2Round.importedConstraints Blake2Round.setupTable) = L) {n : Nat}
    {hn : n < L.length} (index : n = 59) : (L.get ⟨n, hn⟩).Contains (Verification.environment w) := by
  subst hp
  refine contains_xor hL (Blake2Round.importedConstraints.lookup_59 _ (query_lt (by decide))) index (Or.inl ⟨rfl, rfl⟩) rows.q9 ?_ ?_ ?_ ?_ ?_ ?_
  all_goals column_eq

private theorem column_lookup_60 {L : List (Lookup (ZMod p))}
    (hL : FlatOperation.lookups (Blake2Round.importedConstraints Blake2Round.setupTable) = L) {n : Nat}
    {hn : n < L.length} (index : n = 60) : (L.get ⟨n, hn⟩).Contains (Verification.environment w) := by
  subst hp
  refine contains_carry hL (Blake2Round.importedConstraints.lookup_60 _ (query_lt (by decide))) index (Or.inl ⟨rfl, rfl⟩) rows.q10 rows.kb0 ?_ ?_ ?_ ?_ ?_ ?_
  all_goals column_eq

private theorem column_lookup_61 {L : List (Lookup (ZMod p))}
    (hL : FlatOperation.lookups (Blake2Round.importedConstraints Blake2Round.setupTable) = L) {n : Nat}
    {hn : n < L.length} (index : n = 61) : (L.get ⟨n, hn⟩).Contains (Verification.environment w) := by
  subst hp
  refine contains_carry hL (Blake2Round.importedConstraints.lookup_61 _ (query_lt (by decide))) index (Or.inl ⟨rfl, rfl⟩) rows.q11 rows.kb1 ?_ ?_ ?_ ?_ ?_ ?_
  all_goals column_eq

private theorem column_lookup_62 {L : List (Lookup (ZMod p))}
    (hL : FlatOperation.lookups (Blake2Round.importedConstraints Blake2Round.setupTable) = L) {n : Nat}
    {hn : n < L.length} (index : n = 62) : (L.get ⟨n, hn⟩).Contains (Verification.environment w) := by
  subst hp
  refine contains_xor hL (Blake2Round.importedConstraints.lookup_62 _ (query_lt (by decide))) index (Or.inr (Or.inr ⟨rfl, rfl⟩)) rows.q12 ?_ ?_ ?_ ?_ ?_ ?_
  all_goals column_eq

private theorem column_lookup_63 {L : List (Lookup (ZMod p))}
    (hL : FlatOperation.lookups (Blake2Round.importedConstraints Blake2Round.setupTable) = L) {n : Nat}
    {hn : n < L.length} (index : n = 63) : (L.get ⟨n, hn⟩).Contains (Verification.environment w) := by
  subst hp
  refine contains_xor hL (Blake2Round.importedConstraints.lookup_63 _ (query_lt (by decide))) index (Or.inr (Or.inr ⟨rfl, rfl⟩)) rows.q13 ?_ ?_ ?_ ?_ ?_ ?_
  all_goals column_eq

private theorem column_lookup_64 {L : List (Lookup (ZMod p))}
    (hL : FlatOperation.lookups (Blake2Round.importedConstraints Blake2Round.setupTable) = L) {n : Nat}
    {hn : n < L.length} (index : n = 64) : (L.get ⟨n, hn⟩).Contains (Verification.environment w) := by
  subst hp
  refine contains_xor hL (Blake2Round.importedConstraints.lookup_64 _ (query_lt (by decide))) index (Or.inr (Or.inl ⟨rfl, rfl⟩)) rows.q14 ?_ ?_ ?_ ?_ ?_ ?_
  all_goals column_eq

private theorem column_lookup_65 {L : List (Lookup (ZMod p))}
    (hL : FlatOperation.lookups (Blake2Round.importedConstraints Blake2Round.setupTable) = L) {n : Nat}
    {hn : n < L.length} (index : n = 65) : (L.get ⟨n, hn⟩).Contains (Verification.environment w) := by
  subst hp
  refine contains_xor hL (Blake2Round.importedConstraints.lookup_65 _ (query_lt (by decide))) index (Or.inr (Or.inl ⟨rfl, rfl⟩)) rows.q15 ?_ ?_ ?_ ?_ ?_ ?_
  all_goals column_eq

theorem column_lookups_3 {L : List (Lookup (ZMod p))}
    (hL : FlatOperation.lookups (Blake2Round.importedConstraints Blake2Round.setupTable) = L) (n : Nat)
    (hn : n < L.length) (lower : 50 ≤ n) (upper : n < 66) :
    (L.get ⟨n, hn⟩).Contains (Verification.environment w) := by
  rcases (by omega : n = 50 ∨ n = 51 ∨ n = 52 ∨ n = 53 ∨ n = 54 ∨ n = 55 ∨ n = 56 ∨ n = 57 ∨ n = 58 ∨ n = 59 ∨ n = 60 ∨ n = 61 ∨ n = 62 ∨ n = 63 ∨ n = 64 ∨ n = 65) with
    index | index | index | index | index | index | index | index | index | index | index | index | index | index | index | index
  · exact column_lookup_50 hp w rows hL index
  · exact column_lookup_51 hp w rows hL index
  · exact column_lookup_52 hp w rows hL index
  · exact column_lookup_53 hp w rows hL index
  · exact column_lookup_54 hp w rows hL index
  · exact column_lookup_55 hp w rows hL index
  · exact column_lookup_56 hp w rows hL index
  · exact column_lookup_57 hp w rows hL index
  · exact column_lookup_58 hp w rows hL index
  · exact column_lookup_59 hp w rows hL index
  · exact column_lookup_60 hp w rows hL index
  · exact column_lookup_61 hp w rows hL index
  · exact column_lookup_62 hp w rows hL index
  · exact column_lookup_63 hp w rows hL index
  · exact column_lookup_64 hp w rows hL index
  · exact column_lookup_65 hp w rows hL index

end Airbender.NonVacuous.Blake2RoundSpan
