module
public import Slop.NonVacuous.Blake2RoundSpan.FinalEval

@[expose] public section

/-! The final-XOR queries of chaining word 4 (imported lookups 162 to 169) hold for the
    honest assignment of valid inputs over BabyBear: four per limb, each a plain XOR of chunks of the chaining limb
    and the two extended words (`RowInput.finalSlot`). -/

namespace Airbender.NonVacuous.Blake2RoundSpan
open Blake2Round.Proofs

variable {p : Nat} [Fact p.Prime] (hp : p = 2013265921) {x : RowInput} (valid : x.Valid)
include hp valid

private theorem final_lookup_162 {L : List (Lookup (ZMod p))}
    (hL : FlatOperation.lookups (Blake2Round.importedConstraints Blake2Round.setupTable) = L) {n : Nat}
    {hn : n < L.length} (index : n = 162) : (L.get ⟨n, hn⟩).Contains (Verification.environment x.assignment) := by
  subst hp
  final_bounds_high valid 4 0 1 3
  refine contains_xor hL (Blake2Round.importedConstraints.lookup_162 _ (query_lt (by decide))) index (Or.inr (Or.inr ⟨rfl, rfl⟩))
    (chunkXor_cast (w := 9) (m := (x.diagCall 3).xf1) (n := x.finalSlot 4 0 0) (k := x.finalSlot 4 0 1) (by final_unfold) (by final_unfold) (by final_unfold) (by decide)
      (by final_unfold)) ?_ ?_ ?_ ?_ ?_ ?_
  · honest_entry
  · honest_entry
  · honest_entry
  · honest_entry
  · honest_entry
  · honest_entry

private theorem final_lookup_163 {L : List (Lookup (ZMod p))}
    (hL : FlatOperation.lookups (Blake2Round.importedConstraints Blake2Round.setupTable) = L) {n : Nat}
    {hn : n < L.length} (index : n = 163) : (L.get ⟨n, hn⟩).Contains (Verification.environment x.assignment) := by
  subst hp
  final_bounds_high valid 4 0 1 3
  refine contains_xor hL (Blake2Round.importedConstraints.lookup_163 _ (query_lt (by decide))) index (Or.inr (Or.inl ⟨rfl, rfl⟩))
    (chunkXor_cast (w := 7) (m := (x.diagCall 3).xf2) (n := (x.state 4).lo / 512) (k := x.finalSlot 4 0 2) (by final_unfold) (by final_unfold) (by final_unfold) (by decide)
      (by final_unfold)) ?_ ?_ ?_ ?_ ?_ ?_
  · honest_entry
  · honest_entry
    field_identity (-3932160) (show (x.diagCall 3).b2lo = (x.diagCall 3).xf1 + 512 * (x.diagCall 3).xf2 from rfl)
  · honest_entry
    field_identity (-3932160) (show (x.state 4).lo = x.finalSlot 4 0 0 + 512 * ((x.state 4).lo / 512) by final_unfold)
  · honest_entry
  · honest_entry
  · honest_entry

private theorem final_lookup_164 {L : List (Lookup (ZMod p))}
    (hL : FlatOperation.lookups (Blake2Round.importedConstraints Blake2Round.setupTable) = L) {n : Nat}
    {hn : n < L.length} (index : n = 164) : (L.get ⟨n, hn⟩).Contains (Verification.environment x.assignment) := by
  subst hp
  final_bounds_high valid 4 0 1 3
  refine contains_xor hL (Blake2Round.importedConstraints.lookup_164 _ (query_lt (by decide))) index (Or.inl ⟨rfl, rfl⟩)
    (chunkXor_cast (w := 8) (m := (x.diagCall 1).xe1) (n := x.finalSlot 4 0 1 % 256) (k := x.finalSlot 4 0 4) (by final_unfold) (by final_unfold) (by final_unfold) (by decide)
      (by final_unfold)) ?_ ?_ ?_ ?_ ?_ ?_
  · honest_entry
  · honest_entry
  · honest_entry
    field_identity 1 (show x.finalSlot 4 0 1 = x.finalSlot 4 0 1 % 256 + 256 * x.finalSlot 4 0 3 by final_unfold)
  · honest_entry
  · honest_entry
  · honest_entry

private theorem final_lookup_165 {L : List (Lookup (ZMod p))}
    (hL : FlatOperation.lookups (Blake2Round.importedConstraints Blake2Round.setupTable) = L) {n : Nat}
    {hn : n < L.length} (index : n = 165) : (L.get ⟨n, hn⟩).Contains (Verification.environment x.assignment) := by
  subst hp
  final_bounds_high valid 4 0 1 3
  refine contains_xor hL (Blake2Round.importedConstraints.lookup_165 _ (query_lt (by decide))) index (Or.inl ⟨rfl, rfl⟩)
    (chunkXor_cast (w := 8) (m := (x.diagCall 1).xe2) (n := x.finalSlot 4 0 3 + 2 * x.finalSlot 4 0 2) (k := x.finalSlot 4 0 5) (by final_unfold) (by final_unfold) (by final_unfold) (by decide)
      (by final_unfold)) ?_ ?_ ?_ ?_ ?_ ?_
  · honest_entry
  · honest_entry
    field_identity (-7864320) (show (x.diagCall 1).d2lo = (x.diagCall 1).xe1 + 256 * (x.diagCall 1).xe2 from rfl)
  · honest_entry
    push_cast
    ring
  · honest_entry
  · honest_entry
  · honest_entry

private theorem final_lookup_166 {L : List (Lookup (ZMod p))}
    (hL : FlatOperation.lookups (Blake2Round.importedConstraints Blake2Round.setupTable) = L) {n : Nat}
    {hn : n < L.length} (index : n = 166) : (L.get ⟨n, hn⟩).Contains (Verification.environment x.assignment) := by
  subst hp
  final_bounds_high valid 4 1 1 3
  refine contains_xor hL (Blake2Round.importedConstraints.lookup_166 _ (query_lt (by decide))) index (Or.inr (Or.inr ⟨rfl, rfl⟩))
    (chunkXor_cast (w := 9) (m := (x.diagCall 3).xf3) (n := x.finalSlot 4 1 0) (k := x.finalSlot 4 1 1) (by final_unfold) (by final_unfold) (by final_unfold) (by decide)
      (by final_unfold)) ?_ ?_ ?_ ?_ ?_ ?_
  · honest_entry
  · honest_entry
  · honest_entry
  · honest_entry
  · honest_entry
  · honest_entry

private theorem final_lookup_167 {L : List (Lookup (ZMod p))}
    (hL : FlatOperation.lookups (Blake2Round.importedConstraints Blake2Round.setupTable) = L) {n : Nat}
    {hn : n < L.length} (index : n = 167) : (L.get ⟨n, hn⟩).Contains (Verification.environment x.assignment) := by
  subst hp
  final_bounds_high valid 4 1 1 3
  refine contains_xor hL (Blake2Round.importedConstraints.lookup_167 _ (query_lt (by decide))) index (Or.inr (Or.inl ⟨rfl, rfl⟩))
    (chunkXor_cast (w := 7) (m := (x.diagCall 3).xf0) (n := (x.state 4).hi / 512) (k := x.finalSlot 4 1 2) (by final_unfold) (by final_unfold) (by final_unfold) (by decide)
      (by final_unfold)) ?_ ?_ ?_ ?_ ?_ ?_
  · honest_entry
  · honest_entry
    field_identity (-3932160) (show (x.diagCall 3).b2hi = (x.diagCall 3).xf3 + 512 * (x.diagCall 3).xf0 from rfl)
  · honest_entry
    field_identity (-3932160) (show (x.state 4).hi = x.finalSlot 4 1 0 + 512 * ((x.state 4).hi / 512) by final_unfold)
  · honest_entry
  · honest_entry
  · honest_entry

private theorem final_lookup_168 {L : List (Lookup (ZMod p))}
    (hL : FlatOperation.lookups (Blake2Round.importedConstraints Blake2Round.setupTable) = L) {n : Nat}
    {hn : n < L.length} (index : n = 168) : (L.get ⟨n, hn⟩).Contains (Verification.environment x.assignment) := by
  subst hp
  final_bounds_high valid 4 1 1 3
  refine contains_xor hL (Blake2Round.importedConstraints.lookup_168 _ (query_lt (by decide))) index (Or.inl ⟨rfl, rfl⟩)
    (chunkXor_cast (w := 8) (m := (x.diagCall 1).xe3) (n := x.finalSlot 4 1 1 % 256) (k := x.finalSlot 4 1 4) (by final_unfold) (by final_unfold) (by final_unfold) (by decide)
      (by final_unfold)) ?_ ?_ ?_ ?_ ?_ ?_
  · honest_entry
  · honest_entry
  · honest_entry
    field_identity 1 (show x.finalSlot 4 1 1 = x.finalSlot 4 1 1 % 256 + 256 * x.finalSlot 4 1 3 by final_unfold)
  · honest_entry
  · honest_entry
  · honest_entry

private theorem final_lookup_169 {L : List (Lookup (ZMod p))}
    (hL : FlatOperation.lookups (Blake2Round.importedConstraints Blake2Round.setupTable) = L) {n : Nat}
    {hn : n < L.length} (index : n = 169) : (L.get ⟨n, hn⟩).Contains (Verification.environment x.assignment) := by
  subst hp
  final_bounds_high valid 4 1 1 3
  refine contains_xor hL (Blake2Round.importedConstraints.lookup_169 _ (query_lt (by decide))) index (Or.inl ⟨rfl, rfl⟩)
    (chunkXor_cast (w := 8) (m := (x.diagCall 1).xe0) (n := x.finalSlot 4 1 3 + 2 * x.finalSlot 4 1 2) (k := x.finalSlot 4 1 5) (by final_unfold) (by final_unfold) (by final_unfold) (by decide)
      (by final_unfold)) ?_ ?_ ?_ ?_ ?_ ?_
  · honest_entry
  · honest_entry
    field_identity (-7864320) (show (x.diagCall 1).d2hi = (x.diagCall 1).xe3 + 256 * (x.diagCall 1).xe0 from rfl)
  · honest_entry
    push_cast
    ring
  · honest_entry
  · honest_entry
  · honest_entry

theorem final_lookups_4 {L : List (Lookup (ZMod p))}
    (hL : FlatOperation.lookups (Blake2Round.importedConstraints Blake2Round.setupTable) = L) (n : Nat)
    (hn : n < L.length) (lower : 162 ≤ n) (upper : n < 170) :
    (L.get ⟨n, hn⟩).Contains (Verification.environment x.assignment) := by
  rcases (by omega : n = 162 ∨ n = 163 ∨ n = 164 ∨ n = 165 ∨ n = 166 ∨ n = 167 ∨ n = 168 ∨ n = 169) with
    index | index | index | index | index | index | index | index
  · exact final_lookup_162 hp valid hL index
  · exact final_lookup_163 hp valid hL index
  · exact final_lookup_164 hp valid hL index
  · exact final_lookup_165 hp valid hL index
  · exact final_lookup_166 hp valid hL index
  · exact final_lookup_167 hp valid hL index
  · exact final_lookup_168 hp valid hL index
  · exact final_lookup_169 hp valid hL index

end Airbender.NonVacuous.Blake2RoundSpan
