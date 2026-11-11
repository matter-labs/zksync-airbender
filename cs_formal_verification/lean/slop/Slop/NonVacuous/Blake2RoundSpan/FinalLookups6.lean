module
public import Slop.NonVacuous.Blake2RoundSpan.FinalEval

@[expose] public section

/-! The final-XOR queries of chaining word 6 (imported lookups 178 to 185) hold for the
    honest assignment of valid inputs over BabyBear: four per limb, each a plain XOR of chunks of the chaining limb
    and the two extended words (`RowInput.finalSlot`). -/

namespace Airbender.NonVacuous.Blake2RoundSpan
open Blake2Round.Proofs

variable {p : Nat} [Fact p.Prime] (hp : p = 2013265921) {x : RowInput} (valid : x.Valid)
include hp valid

private theorem final_lookup_178 {L : List (Lookup (ZMod p))}
    (hL : FlatOperation.lookups (Blake2Round.importedConstraints Blake2Round.setupTable) = L) {n : Nat}
    {hn : n < L.length} (index : n = 178) : (L.get ⟨n, hn⟩).Contains (Verification.environment x.assignment) := by
  subst hp
  final_bounds_high valid 6 0 1 3
  refine contains_xor hL (Blake2Round.importedConstraints.lookup_178 _ (query_lt (by decide))) index (Or.inr (Or.inr ⟨rfl, rfl⟩))
    (chunkXor_cast (w := 9) (m := (x.diagCall 1).xf1) (n := x.finalSlot 6 0 0) (k := x.finalSlot 6 0 1) (by final_unfold) (by final_unfold) (by final_unfold) (by decide)
      (by final_unfold)) ?_ ?_ ?_ ?_ ?_ ?_
  · honest_entry
  · honest_entry
  · honest_entry
  · honest_entry
  · honest_entry
  · honest_entry

private theorem final_lookup_179 {L : List (Lookup (ZMod p))}
    (hL : FlatOperation.lookups (Blake2Round.importedConstraints Blake2Round.setupTable) = L) {n : Nat}
    {hn : n < L.length} (index : n = 179) : (L.get ⟨n, hn⟩).Contains (Verification.environment x.assignment) := by
  subst hp
  final_bounds_high valid 6 0 1 3
  refine contains_xor hL (Blake2Round.importedConstraints.lookup_179 _ (query_lt (by decide))) index (Or.inr (Or.inl ⟨rfl, rfl⟩))
    (chunkXor_cast (w := 7) (m := (x.diagCall 1).xf2) (n := (x.state 6).lo / 512) (k := x.finalSlot 6 0 2) (by final_unfold) (by final_unfold) (by final_unfold) (by decide)
      (by final_unfold)) ?_ ?_ ?_ ?_ ?_ ?_
  · honest_entry
  · honest_entry
    field_identity (-3932160) (show (x.diagCall 1).b2lo = (x.diagCall 1).xf1 + 512 * (x.diagCall 1).xf2 from rfl)
  · honest_entry
    field_identity (-3932160) (show (x.state 6).lo = x.finalSlot 6 0 0 + 512 * ((x.state 6).lo / 512) by final_unfold)
  · honest_entry
  · honest_entry
  · honest_entry

private theorem final_lookup_180 {L : List (Lookup (ZMod p))}
    (hL : FlatOperation.lookups (Blake2Round.importedConstraints Blake2Round.setupTable) = L) {n : Nat}
    {hn : n < L.length} (index : n = 180) : (L.get ⟨n, hn⟩).Contains (Verification.environment x.assignment) := by
  subst hp
  final_bounds_high valid 6 0 1 3
  refine contains_xor hL (Blake2Round.importedConstraints.lookup_180 _ (query_lt (by decide))) index (Or.inl ⟨rfl, rfl⟩)
    (chunkXor_cast (w := 8) (m := (x.diagCall 3).xe1) (n := x.finalSlot 6 0 1 % 256) (k := x.finalSlot 6 0 4) (by final_unfold) (by final_unfold) (by final_unfold) (by decide)
      (by final_unfold)) ?_ ?_ ?_ ?_ ?_ ?_
  · honest_entry
  · honest_entry
  · honest_entry
    field_identity 1 (show x.finalSlot 6 0 1 = x.finalSlot 6 0 1 % 256 + 256 * x.finalSlot 6 0 3 by final_unfold)
  · honest_entry
  · honest_entry
  · honest_entry

private theorem final_lookup_181 {L : List (Lookup (ZMod p))}
    (hL : FlatOperation.lookups (Blake2Round.importedConstraints Blake2Round.setupTable) = L) {n : Nat}
    {hn : n < L.length} (index : n = 181) : (L.get ⟨n, hn⟩).Contains (Verification.environment x.assignment) := by
  subst hp
  final_bounds_high valid 6 0 1 3
  refine contains_xor hL (Blake2Round.importedConstraints.lookup_181 _ (query_lt (by decide))) index (Or.inl ⟨rfl, rfl⟩)
    (chunkXor_cast (w := 8) (m := (x.diagCall 3).xe2) (n := x.finalSlot 6 0 3 + 2 * x.finalSlot 6 0 2) (k := x.finalSlot 6 0 5) (by final_unfold) (by final_unfold) (by final_unfold) (by decide)
      (by final_unfold)) ?_ ?_ ?_ ?_ ?_ ?_
  · honest_entry
  · honest_entry
    field_identity (-7864320) (show (x.diagCall 3).d2lo = (x.diagCall 3).xe1 + 256 * (x.diagCall 3).xe2 from rfl)
  · honest_entry
    push_cast
    ring
  · honest_entry
  · honest_entry
  · honest_entry

private theorem final_lookup_182 {L : List (Lookup (ZMod p))}
    (hL : FlatOperation.lookups (Blake2Round.importedConstraints Blake2Round.setupTable) = L) {n : Nat}
    {hn : n < L.length} (index : n = 182) : (L.get ⟨n, hn⟩).Contains (Verification.environment x.assignment) := by
  subst hp
  final_bounds_high valid 6 1 1 3
  refine contains_xor hL (Blake2Round.importedConstraints.lookup_182 _ (query_lt (by decide))) index (Or.inr (Or.inr ⟨rfl, rfl⟩))
    (chunkXor_cast (w := 9) (m := (x.diagCall 1).xf3) (n := x.finalSlot 6 1 0) (k := x.finalSlot 6 1 1) (by final_unfold) (by final_unfold) (by final_unfold) (by decide)
      (by final_unfold)) ?_ ?_ ?_ ?_ ?_ ?_
  · honest_entry
  · honest_entry
  · honest_entry
  · honest_entry
  · honest_entry
  · honest_entry

private theorem final_lookup_183 {L : List (Lookup (ZMod p))}
    (hL : FlatOperation.lookups (Blake2Round.importedConstraints Blake2Round.setupTable) = L) {n : Nat}
    {hn : n < L.length} (index : n = 183) : (L.get ⟨n, hn⟩).Contains (Verification.environment x.assignment) := by
  subst hp
  final_bounds_high valid 6 1 1 3
  refine contains_xor hL (Blake2Round.importedConstraints.lookup_183 _ (query_lt (by decide))) index (Or.inr (Or.inl ⟨rfl, rfl⟩))
    (chunkXor_cast (w := 7) (m := (x.diagCall 1).xf0) (n := (x.state 6).hi / 512) (k := x.finalSlot 6 1 2) (by final_unfold) (by final_unfold) (by final_unfold) (by decide)
      (by final_unfold)) ?_ ?_ ?_ ?_ ?_ ?_
  · honest_entry
  · honest_entry
    field_identity (-3932160) (show (x.diagCall 1).b2hi = (x.diagCall 1).xf3 + 512 * (x.diagCall 1).xf0 from rfl)
  · honest_entry
    field_identity (-3932160) (show (x.state 6).hi = x.finalSlot 6 1 0 + 512 * ((x.state 6).hi / 512) by final_unfold)
  · honest_entry
  · honest_entry
  · honest_entry

private theorem final_lookup_184 {L : List (Lookup (ZMod p))}
    (hL : FlatOperation.lookups (Blake2Round.importedConstraints Blake2Round.setupTable) = L) {n : Nat}
    {hn : n < L.length} (index : n = 184) : (L.get ⟨n, hn⟩).Contains (Verification.environment x.assignment) := by
  subst hp
  final_bounds_high valid 6 1 1 3
  refine contains_xor hL (Blake2Round.importedConstraints.lookup_184 _ (query_lt (by decide))) index (Or.inl ⟨rfl, rfl⟩)
    (chunkXor_cast (w := 8) (m := (x.diagCall 3).xe3) (n := x.finalSlot 6 1 1 % 256) (k := x.finalSlot 6 1 4) (by final_unfold) (by final_unfold) (by final_unfold) (by decide)
      (by final_unfold)) ?_ ?_ ?_ ?_ ?_ ?_
  · honest_entry
  · honest_entry
  · honest_entry
    field_identity 1 (show x.finalSlot 6 1 1 = x.finalSlot 6 1 1 % 256 + 256 * x.finalSlot 6 1 3 by final_unfold)
  · honest_entry
  · honest_entry
  · honest_entry

private theorem final_lookup_185 {L : List (Lookup (ZMod p))}
    (hL : FlatOperation.lookups (Blake2Round.importedConstraints Blake2Round.setupTable) = L) {n : Nat}
    {hn : n < L.length} (index : n = 185) : (L.get ⟨n, hn⟩).Contains (Verification.environment x.assignment) := by
  subst hp
  final_bounds_high valid 6 1 1 3
  refine contains_xor hL (Blake2Round.importedConstraints.lookup_185 _ (query_lt (by decide))) index (Or.inl ⟨rfl, rfl⟩)
    (chunkXor_cast (w := 8) (m := (x.diagCall 3).xe0) (n := x.finalSlot 6 1 3 + 2 * x.finalSlot 6 1 2) (k := x.finalSlot 6 1 5) (by final_unfold) (by final_unfold) (by final_unfold) (by decide)
      (by final_unfold)) ?_ ?_ ?_ ?_ ?_ ?_
  · honest_entry
  · honest_entry
    field_identity (-7864320) (show (x.diagCall 3).d2hi = (x.diagCall 3).xe3 + 256 * (x.diagCall 3).xe0 from rfl)
  · honest_entry
    push_cast
    ring
  · honest_entry
  · honest_entry
  · honest_entry

theorem final_lookups_6 {L : List (Lookup (ZMod p))}
    (hL : FlatOperation.lookups (Blake2Round.importedConstraints Blake2Round.setupTable) = L) (n : Nat)
    (hn : n < L.length) (lower : 178 ≤ n) (upper : n < 186) :
    (L.get ⟨n, hn⟩).Contains (Verification.environment x.assignment) := by
  rcases (by omega : n = 178 ∨ n = 179 ∨ n = 180 ∨ n = 181 ∨ n = 182 ∨ n = 183 ∨ n = 184 ∨ n = 185) with
    index | index | index | index | index | index | index | index
  · exact final_lookup_178 hp valid hL index
  · exact final_lookup_179 hp valid hL index
  · exact final_lookup_180 hp valid hL index
  · exact final_lookup_181 hp valid hL index
  · exact final_lookup_182 hp valid hL index
  · exact final_lookup_183 hp valid hL index
  · exact final_lookup_184 hp valid hL index
  · exact final_lookup_185 hp valid hL index

end Airbender.NonVacuous.Blake2RoundSpan
