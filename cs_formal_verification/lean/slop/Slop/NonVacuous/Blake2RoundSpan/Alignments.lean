module
public import Slop.NonVacuous.Blake2RoundSpan.AssertEval

@[expose] public section

/-! The two pointer-alignment queries of an honest round row (imported lookups 0 and 1) hold over BabyBear: the state pointer is 128-aligned, the message pointer 64-aligned. -/

namespace Airbender.NonVacuous.Blake2RoundSpan

variable {p : Nat} [Fact p.Prime] (hp : p = 2013265921) {x : RowInput} (valid : x.Valid)
include hp valid

private theorem alignment_0 {L : List (Lookup (ZMod p))}
    (hL : FlatOperation.lookups (Blake2Round.importedConstraints (p := p) Blake2Round.setupTable) = L) {n : Nat}
    {hn : n < L.length} (index : n = 0) : (L.get ⟨n, hn⟩).Contains (Verification.environment x.assignment) := by
  subst hp hL index
  rw [Blake2Round.importedConstraints.lookup_0]
  have pointer := valid.statePointer
  simp only [Arithmetic.Word.Bounded, Arithmetic.limbBase] at pointer
  refine range_of_eval (n := x.statePointer.lo / 128) ?_ (by simp only [Trace.timestampBase]; omega) (by decide)
  honest_entry
  honest_value
  field_identity (-15728640) (show x.statePointer.lo = 128 * (x.statePointer.lo / 128) by omega)

private theorem alignment_1 {L : List (Lookup (ZMod p))}
    (hL : FlatOperation.lookups (Blake2Round.importedConstraints (p := p) Blake2Round.setupTable) = L) {n : Nat}
    {hn : n < L.length} (index : n = 1) : (L.get ⟨n, hn⟩).Contains (Verification.environment x.assignment) := by
  subst hp hL index
  rw [Blake2Round.importedConstraints.lookup_1]
  have pointer := valid.messagePointer
  simp only [Arithmetic.Word.Bounded, Arithmetic.limbBase] at pointer
  refine range_of_eval (n := x.messagePointer.lo / 64) ?_ (by simp only [Trace.timestampBase]; omega) (by decide)
  honest_entry
  honest_value
  field_identity (-31457280) (show x.messagePointer.lo = 64 * (x.messagePointer.lo / 64) by omega)

theorem alignments {L : List (Lookup (ZMod p))}
    (hL : FlatOperation.lookups (Blake2Round.importedConstraints (p := p) Blake2Round.setupTable) = L) (n : Nat) (hn : n < L.length)
    (upper : n ≤ 1) :
    (L.get ⟨n, hn⟩).Contains (Verification.environment x.assignment) := by
  rcases (by omega : n = 0 ∨ n = 1) with
    index | index
  · exact alignment_0 hp valid hL index
  · exact alignment_1 hp valid hL index

end Airbender.NonVacuous.Blake2RoundSpan
