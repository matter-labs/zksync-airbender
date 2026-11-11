module
public import Slop.NonVacuous.Blake2RoundSpan.Queries
public import Slop.Blake2Round.ColumnG

@[expose] public section

/-! The sixteen fixed-table queries of column G call 1 (imported lookups 18 to 33) hold over BabyBear
    when its trace's table facts do (`Blake2Round.Proofs.GTrace.Rows`), for any assignment: one lemma per query,
    whose entries evaluate to the trace's fields (`column_eq`). -/

namespace Airbender.NonVacuous.Blake2RoundSpan
open Blake2Round.Proofs

variable {p : Nat} [Fact p.Prime] (hp : p = 2013265921) (w : Nat → ZMod p) (rows : (columnTrace 1 w).Rows)
include hp rows

private theorem column_lookup_18 {L : List (Lookup (ZMod p))}
    (hL : FlatOperation.lookups (Blake2Round.importedConstraints Blake2Round.setupTable) = L) {n : Nat}
    {hn : n < L.length} (index : n = 18) : (L.get ⟨n, hn⟩).Contains (Verification.environment w) := by
  subst hp
  refine contains_carry hL (Blake2Round.importedConstraints.lookup_18 _ (query_lt (by decide))) index (Or.inl ⟨rfl, rfl⟩) rows.q0 rows.ka0 ?_ ?_ ?_ ?_ ?_ ?_
  all_goals column_eq

private theorem column_lookup_19 {L : List (Lookup (ZMod p))}
    (hL : FlatOperation.lookups (Blake2Round.importedConstraints Blake2Round.setupTable) = L) {n : Nat}
    {hn : n < L.length} (index : n = 19) : (L.get ⟨n, hn⟩).Contains (Verification.environment w) := by
  subst hp
  refine contains_xor hL (Blake2Round.importedConstraints.lookup_19 _ (query_lt (by decide))) index (Or.inl ⟨rfl, rfl⟩) rows.q1 ?_ ?_ ?_ ?_ ?_ ?_
  all_goals column_eq

private theorem column_lookup_20 {L : List (Lookup (ZMod p))}
    (hL : FlatOperation.lookups (Blake2Round.importedConstraints Blake2Round.setupTable) = L) {n : Nat}
    {hn : n < L.length} (index : n = 20) : (L.get ⟨n, hn⟩).Contains (Verification.environment w) := by
  subst hp
  refine contains_carry hL (Blake2Round.importedConstraints.lookup_20 _ (query_lt (by decide))) index (Or.inl ⟨rfl, rfl⟩) rows.q2 rows.ka1 ?_ ?_ ?_ ?_ ?_ ?_
  all_goals column_eq

private theorem column_lookup_21 {L : List (Lookup (ZMod p))}
    (hL : FlatOperation.lookups (Blake2Round.importedConstraints Blake2Round.setupTable) = L) {n : Nat}
    {hn : n < L.length} (index : n = 21) : (L.get ⟨n, hn⟩).Contains (Verification.environment w) := by
  subst hp
  refine contains_xor hL (Blake2Round.importedConstraints.lookup_21 _ (query_lt (by decide))) index (Or.inl ⟨rfl, rfl⟩) rows.q3 ?_ ?_ ?_ ?_ ?_ ?_
  all_goals column_eq

private theorem column_lookup_22 {L : List (Lookup (ZMod p))}
    (hL : FlatOperation.lookups (Blake2Round.importedConstraints Blake2Round.setupTable) = L) {n : Nat}
    {hn : n < L.length} (index : n = 22) : (L.get ⟨n, hn⟩).Contains (Verification.environment w) := by
  subst hp
  refine contains_xor hL (Blake2Round.importedConstraints.lookup_22 _ (query_lt (by decide))) index (Or.inr (Or.inr ⟨rfl, rfl⟩)) rows.q4 ?_ ?_ ?_ ?_ ?_ ?_
  all_goals column_eq

private theorem column_lookup_23 {L : List (Lookup (ZMod p))}
    (hL : FlatOperation.lookups (Blake2Round.importedConstraints Blake2Round.setupTable) = L) {n : Nat}
    {hn : n < L.length} (index : n = 23) : (L.get ⟨n, hn⟩).Contains (Verification.environment w) := by
  subst hp
  refine contains_xor hL (Blake2Round.importedConstraints.lookup_23 _ (query_lt (by decide))) index (Or.inr (Or.inr ⟨rfl, rfl⟩)) rows.q5 ?_ ?_ ?_ ?_ ?_ ?_
  all_goals column_eq

private theorem column_lookup_24 {L : List (Lookup (ZMod p))}
    (hL : FlatOperation.lookups (Blake2Round.importedConstraints Blake2Round.setupTable) = L) {n : Nat}
    {hn : n < L.length} (index : n = 24) : (L.get ⟨n, hn⟩).Contains (Verification.environment w) := by
  subst hp
  refine contains_split hL (Blake2Round.importedConstraints.lookup_24 _ (query_lt (by decide))) index rows.q6 ?_ ?_ ?_ ?_ ?_ ?_
  all_goals column_eq

private theorem column_lookup_25 {L : List (Lookup (ZMod p))}
    (hL : FlatOperation.lookups (Blake2Round.importedConstraints Blake2Round.setupTable) = L) {n : Nat}
    {hn : n < L.length} (index : n = 25) : (L.get ⟨n, hn⟩).Contains (Verification.environment w) := by
  subst hp
  refine contains_split hL (Blake2Round.importedConstraints.lookup_25 _ (query_lt (by decide))) index rows.q7 ?_ ?_ ?_ ?_ ?_ ?_
  all_goals column_eq

private theorem column_lookup_26 {L : List (Lookup (ZMod p))}
    (hL : FlatOperation.lookups (Blake2Round.importedConstraints Blake2Round.setupTable) = L) {n : Nat}
    {hn : n < L.length} (index : n = 26) : (L.get ⟨n, hn⟩).Contains (Verification.environment w) := by
  subst hp
  refine contains_xor hL (Blake2Round.importedConstraints.lookup_26 _ (query_lt (by decide))) index (Or.inl ⟨rfl, rfl⟩) rows.q8 ?_ ?_ ?_ ?_ ?_ ?_
  all_goals column_eq

private theorem column_lookup_27 {L : List (Lookup (ZMod p))}
    (hL : FlatOperation.lookups (Blake2Round.importedConstraints Blake2Round.setupTable) = L) {n : Nat}
    {hn : n < L.length} (index : n = 27) : (L.get ⟨n, hn⟩).Contains (Verification.environment w) := by
  subst hp
  refine contains_xor hL (Blake2Round.importedConstraints.lookup_27 _ (query_lt (by decide))) index (Or.inl ⟨rfl, rfl⟩) rows.q9 ?_ ?_ ?_ ?_ ?_ ?_
  all_goals column_eq

private theorem column_lookup_28 {L : List (Lookup (ZMod p))}
    (hL : FlatOperation.lookups (Blake2Round.importedConstraints Blake2Round.setupTable) = L) {n : Nat}
    {hn : n < L.length} (index : n = 28) : (L.get ⟨n, hn⟩).Contains (Verification.environment w) := by
  subst hp
  refine contains_carry hL (Blake2Round.importedConstraints.lookup_28 _ (query_lt (by decide))) index (Or.inl ⟨rfl, rfl⟩) rows.q10 rows.kb0 ?_ ?_ ?_ ?_ ?_ ?_
  all_goals column_eq

private theorem column_lookup_29 {L : List (Lookup (ZMod p))}
    (hL : FlatOperation.lookups (Blake2Round.importedConstraints Blake2Round.setupTable) = L) {n : Nat}
    {hn : n < L.length} (index : n = 29) : (L.get ⟨n, hn⟩).Contains (Verification.environment w) := by
  subst hp
  refine contains_carry hL (Blake2Round.importedConstraints.lookup_29 _ (query_lt (by decide))) index (Or.inl ⟨rfl, rfl⟩) rows.q11 rows.kb1 ?_ ?_ ?_ ?_ ?_ ?_
  all_goals column_eq

private theorem column_lookup_30 {L : List (Lookup (ZMod p))}
    (hL : FlatOperation.lookups (Blake2Round.importedConstraints Blake2Round.setupTable) = L) {n : Nat}
    {hn : n < L.length} (index : n = 30) : (L.get ⟨n, hn⟩).Contains (Verification.environment w) := by
  subst hp
  refine contains_xor hL (Blake2Round.importedConstraints.lookup_30 _ (query_lt (by decide))) index (Or.inr (Or.inr ⟨rfl, rfl⟩)) rows.q12 ?_ ?_ ?_ ?_ ?_ ?_
  all_goals column_eq

private theorem column_lookup_31 {L : List (Lookup (ZMod p))}
    (hL : FlatOperation.lookups (Blake2Round.importedConstraints Blake2Round.setupTable) = L) {n : Nat}
    {hn : n < L.length} (index : n = 31) : (L.get ⟨n, hn⟩).Contains (Verification.environment w) := by
  subst hp
  refine contains_xor hL (Blake2Round.importedConstraints.lookup_31 _ (query_lt (by decide))) index (Or.inr (Or.inr ⟨rfl, rfl⟩)) rows.q13 ?_ ?_ ?_ ?_ ?_ ?_
  all_goals column_eq

private theorem column_lookup_32 {L : List (Lookup (ZMod p))}
    (hL : FlatOperation.lookups (Blake2Round.importedConstraints Blake2Round.setupTable) = L) {n : Nat}
    {hn : n < L.length} (index : n = 32) : (L.get ⟨n, hn⟩).Contains (Verification.environment w) := by
  subst hp
  refine contains_xor hL (Blake2Round.importedConstraints.lookup_32 _ (query_lt (by decide))) index (Or.inr (Or.inl ⟨rfl, rfl⟩)) rows.q14 ?_ ?_ ?_ ?_ ?_ ?_
  all_goals column_eq

private theorem column_lookup_33 {L : List (Lookup (ZMod p))}
    (hL : FlatOperation.lookups (Blake2Round.importedConstraints Blake2Round.setupTable) = L) {n : Nat}
    {hn : n < L.length} (index : n = 33) : (L.get ⟨n, hn⟩).Contains (Verification.environment w) := by
  subst hp
  refine contains_xor hL (Blake2Round.importedConstraints.lookup_33 _ (query_lt (by decide))) index (Or.inr (Or.inl ⟨rfl, rfl⟩)) rows.q15 ?_ ?_ ?_ ?_ ?_ ?_
  all_goals column_eq

theorem column_lookups_1 {L : List (Lookup (ZMod p))}
    (hL : FlatOperation.lookups (Blake2Round.importedConstraints Blake2Round.setupTable) = L) (n : Nat)
    (hn : n < L.length) (lower : 18 ≤ n) (upper : n < 34) :
    (L.get ⟨n, hn⟩).Contains (Verification.environment w) := by
  rcases (by omega : n = 18 ∨ n = 19 ∨ n = 20 ∨ n = 21 ∨ n = 22 ∨ n = 23 ∨ n = 24 ∨ n = 25 ∨ n = 26 ∨ n = 27 ∨ n = 28 ∨ n = 29 ∨ n = 30 ∨ n = 31 ∨ n = 32 ∨ n = 33) with
    index | index | index | index | index | index | index | index | index | index | index | index | index | index | index | index
  · exact column_lookup_18 hp w rows hL index
  · exact column_lookup_19 hp w rows hL index
  · exact column_lookup_20 hp w rows hL index
  · exact column_lookup_21 hp w rows hL index
  · exact column_lookup_22 hp w rows hL index
  · exact column_lookup_23 hp w rows hL index
  · exact column_lookup_24 hp w rows hL index
  · exact column_lookup_25 hp w rows hL index
  · exact column_lookup_26 hp w rows hL index
  · exact column_lookup_27 hp w rows hL index
  · exact column_lookup_28 hp w rows hL index
  · exact column_lookup_29 hp w rows hL index
  · exact column_lookup_30 hp w rows hL index
  · exact column_lookup_31 hp w rows hL index
  · exact column_lookup_32 hp w rows hL index
  · exact column_lookup_33 hp w rows hL index

end Airbender.NonVacuous.Blake2RoundSpan
