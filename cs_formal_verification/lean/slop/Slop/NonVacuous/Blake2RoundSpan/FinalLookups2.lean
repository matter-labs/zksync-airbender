module
public import Slop.NonVacuous.Blake2RoundSpan.FinalEval

@[expose] public section

/-! The final-XOR queries of chaining word 2 (imported lookups 146 to 153) hold for the
    honest assignment of valid inputs over BabyBear: four per limb, each a plain XOR of chunks of the chaining limb
    and the two extended words (`RowInput.finalSlot`). -/

namespace Airbender.NonVacuous.Blake2RoundSpan
open Blake2Round.Proofs

variable {p : Nat} [Fact p.Prime] (hp : p = 2013265921) {x : RowInput} (valid : x.Valid)
include hp valid

private theorem final_lookup_146 {L : List (Lookup (ZMod p))}
    (hL : FlatOperation.lookups (Blake2Round.importedConstraints Blake2Round.setupTable) = L) {n : Nat}
    {hn : n < L.length} (index : n = 146) : (L.get ⟨n, hn⟩).Contains (Verification.environment x.assignment) := by
  subst hp
  final_bounds_low valid 2 0 0 2
  refine contains_xor hL (Blake2Round.importedConstraints.lookup_146 _ (query_lt (by decide))) index (Or.inr (Or.inl ⟨rfl, rfl⟩))
    (chunkXor_cast (w := 7) (m := x.finalSlot 2 0 0) (n := (x.diagCall 0).c2lo % 128) (k := x.finalSlot 2 0 1) (by final_unfold) (by final_unfold) (by final_unfold) (by decide)
      (by final_unfold)) ?_ ?_ ?_ ?_ ?_ ?_
  · honest_entry
  · honest_entry
  · honest_entry
  · honest_entry
  · honest_entry
  · honest_entry

private theorem final_lookup_147 {L : List (Lookup (ZMod p))}
    (hL : FlatOperation.lookups (Blake2Round.importedConstraints Blake2Round.setupTable) = L) {n : Nat}
    {hn : n < L.length} (index : n = 147) : (L.get ⟨n, hn⟩).Contains (Verification.environment x.assignment) := by
  subst hp
  final_bounds_low valid 2 0 0 2
  refine contains_xor hL (Blake2Round.importedConstraints.lookup_147 _ (query_lt (by decide))) index (Or.inr (Or.inr ⟨rfl, rfl⟩))
    (chunkXor_cast (w := 9) (m := (x.state 2).lo / 128) (n := (x.diagCall 0).c2lo / 128) (k := x.finalSlot 2 0 2) (by final_unfold) (by final_unfold) (by final_unfold) (by decide)
      (by final_unfold)) ?_ ?_ ?_ ?_ ?_ ?_
  · honest_entry
  · honest_entry
    field_identity (-15728640) (show (x.state 2).lo = x.finalSlot 2 0 0 + 128 * ((x.state 2).lo / 128) by final_unfold)
  · honest_entry
    field_identity (-15728640) (show (x.diagCall 0).c2lo = (x.diagCall 0).c2lo % 128 + 128 * ((x.diagCall 0).c2lo / 128) by final_unfold)
  · honest_entry
  · honest_entry
  · honest_entry

private theorem final_lookup_148 {L : List (Lookup (ZMod p))}
    (hL : FlatOperation.lookups (Blake2Round.importedConstraints Blake2Round.setupTable) = L) {n : Nat}
    {hn : n < L.length} (index : n = 148) : (L.get ⟨n, hn⟩).Contains (Verification.environment x.assignment) := by
  subst hp
  final_bounds_low valid 2 0 0 2
  refine contains_xor hL (Blake2Round.importedConstraints.lookup_148 _ (query_lt (by decide))) index (Or.inr (Or.inl ⟨rfl, rfl⟩))
    (chunkXor_cast (w := 7) (m := x.finalSlot 2 0 1) (n := (x.diagCall 2).a2lo % 128) (k := x.finalSlot 2 0 4) (by final_unfold) (by final_unfold) (by final_unfold) (by decide)
      (by final_unfold)) ?_ ?_ ?_ ?_ ?_ ?_
  · honest_entry
  · honest_entry
  · honest_entry
    field_identity 1 (show (x.diagCall 2).a2lo % 256 = (x.diagCall 2).a2lo % 128 + 128 * x.finalSlot 2 0 3 by final_unfold)
  · honest_entry
  · honest_entry
  · honest_entry

private theorem final_lookup_149 {L : List (Lookup (ZMod p))}
    (hL : FlatOperation.lookups (Blake2Round.importedConstraints Blake2Round.setupTable) = L) {n : Nat}
    {hn : n < L.length} (index : n = 149) : (L.get ⟨n, hn⟩).Contains (Verification.environment x.assignment) := by
  subst hp
  final_bounds_low valid 2 0 0 2
  refine contains_xor hL (Blake2Round.importedConstraints.lookup_149 _ (query_lt (by decide))) index (Or.inr (Or.inr ⟨rfl, rfl⟩))
    (chunkXor_cast (w := 9) (m := x.finalSlot 2 0 2) (n := (x.diagCall 2).a2lo / 128) (k := x.finalSlot 2 0 5) (by final_unfold) (by final_unfold) (by final_unfold) (by decide)
      (by final_unfold)) ?_ ?_ ?_ ?_ ?_ ?_
  · honest_entry
  · honest_entry
  · honest_entry
    field_identity (-15728640) (show (x.diagCall 2).a2lo + 128 * x.finalSlot 2 0 3 = (x.diagCall 2).a2lo % 256 + 128 * ((x.diagCall 2).a2lo / 128) by final_unfold)
  · honest_entry
  · honest_entry
  · honest_entry

private theorem final_lookup_150 {L : List (Lookup (ZMod p))}
    (hL : FlatOperation.lookups (Blake2Round.importedConstraints Blake2Round.setupTable) = L) {n : Nat}
    {hn : n < L.length} (index : n = 150) : (L.get ⟨n, hn⟩).Contains (Verification.environment x.assignment) := by
  subst hp
  final_bounds_low valid 2 1 0 2
  refine contains_xor hL (Blake2Round.importedConstraints.lookup_150 _ (query_lt (by decide))) index (Or.inr (Or.inl ⟨rfl, rfl⟩))
    (chunkXor_cast (w := 7) (m := x.finalSlot 2 1 0) (n := (x.diagCall 0).c2hi % 128) (k := x.finalSlot 2 1 1) (by final_unfold) (by final_unfold) (by final_unfold) (by decide)
      (by final_unfold)) ?_ ?_ ?_ ?_ ?_ ?_
  · honest_entry
  · honest_entry
  · honest_entry
  · honest_entry
  · honest_entry
  · honest_entry

private theorem final_lookup_151 {L : List (Lookup (ZMod p))}
    (hL : FlatOperation.lookups (Blake2Round.importedConstraints Blake2Round.setupTable) = L) {n : Nat}
    {hn : n < L.length} (index : n = 151) : (L.get ⟨n, hn⟩).Contains (Verification.environment x.assignment) := by
  subst hp
  final_bounds_low valid 2 1 0 2
  refine contains_xor hL (Blake2Round.importedConstraints.lookup_151 _ (query_lt (by decide))) index (Or.inr (Or.inr ⟨rfl, rfl⟩))
    (chunkXor_cast (w := 9) (m := (x.state 2).hi / 128) (n := (x.diagCall 0).c2hi / 128) (k := x.finalSlot 2 1 2) (by final_unfold) (by final_unfold) (by final_unfold) (by decide)
      (by final_unfold)) ?_ ?_ ?_ ?_ ?_ ?_
  · honest_entry
  · honest_entry
    field_identity (-15728640) (show (x.state 2).hi = x.finalSlot 2 1 0 + 128 * ((x.state 2).hi / 128) by final_unfold)
  · honest_entry
    field_identity (-15728640) (show (x.diagCall 0).c2hi = (x.diagCall 0).c2hi % 128 + 128 * ((x.diagCall 0).c2hi / 128) by final_unfold)
  · honest_entry
  · honest_entry
  · honest_entry

private theorem final_lookup_152 {L : List (Lookup (ZMod p))}
    (hL : FlatOperation.lookups (Blake2Round.importedConstraints Blake2Round.setupTable) = L) {n : Nat}
    {hn : n < L.length} (index : n = 152) : (L.get ⟨n, hn⟩).Contains (Verification.environment x.assignment) := by
  subst hp
  final_bounds_low valid 2 1 0 2
  refine contains_xor hL (Blake2Round.importedConstraints.lookup_152 _ (query_lt (by decide))) index (Or.inr (Or.inl ⟨rfl, rfl⟩))
    (chunkXor_cast (w := 7) (m := x.finalSlot 2 1 1) (n := (x.diagCall 2).a2hi % 128) (k := x.finalSlot 2 1 4) (by final_unfold) (by final_unfold) (by final_unfold) (by decide)
      (by final_unfold)) ?_ ?_ ?_ ?_ ?_ ?_
  · honest_entry
  · honest_entry
  · honest_entry
    field_identity 1 (show (x.diagCall 2).a2hi % 256 = (x.diagCall 2).a2hi % 128 + 128 * x.finalSlot 2 1 3 by final_unfold)
  · honest_entry
  · honest_entry
  · honest_entry

private theorem final_lookup_153 {L : List (Lookup (ZMod p))}
    (hL : FlatOperation.lookups (Blake2Round.importedConstraints Blake2Round.setupTable) = L) {n : Nat}
    {hn : n < L.length} (index : n = 153) : (L.get ⟨n, hn⟩).Contains (Verification.environment x.assignment) := by
  subst hp
  final_bounds_low valid 2 1 0 2
  refine contains_xor hL (Blake2Round.importedConstraints.lookup_153 _ (query_lt (by decide))) index (Or.inr (Or.inr ⟨rfl, rfl⟩))
    (chunkXor_cast (w := 9) (m := x.finalSlot 2 1 2) (n := (x.diagCall 2).a2hi / 128) (k := x.finalSlot 2 1 5) (by final_unfold) (by final_unfold) (by final_unfold) (by decide)
      (by final_unfold)) ?_ ?_ ?_ ?_ ?_ ?_
  · honest_entry
  · honest_entry
  · honest_entry
    field_identity (-15728640) (show (x.diagCall 2).a2hi + 128 * x.finalSlot 2 1 3 = (x.diagCall 2).a2hi % 256 + 128 * ((x.diagCall 2).a2hi / 128) by final_unfold)
  · honest_entry
  · honest_entry
  · honest_entry

theorem final_lookups_2 {L : List (Lookup (ZMod p))}
    (hL : FlatOperation.lookups (Blake2Round.importedConstraints Blake2Round.setupTable) = L) (n : Nat)
    (hn : n < L.length) (lower : 146 ≤ n) (upper : n < 154) :
    (L.get ⟨n, hn⟩).Contains (Verification.environment x.assignment) := by
  rcases (by omega : n = 146 ∨ n = 147 ∨ n = 148 ∨ n = 149 ∨ n = 150 ∨ n = 151 ∨ n = 152 ∨ n = 153) with
    index | index | index | index | index | index | index | index
  · exact final_lookup_146 hp valid hL index
  · exact final_lookup_147 hp valid hL index
  · exact final_lookup_148 hp valid hL index
  · exact final_lookup_149 hp valid hL index
  · exact final_lookup_150 hp valid hL index
  · exact final_lookup_151 hp valid hL index
  · exact final_lookup_152 hp valid hL index
  · exact final_lookup_153 hp valid hL index

end Airbender.NonVacuous.Blake2RoundSpan
