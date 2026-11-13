module
public import Proven.NonVacuous.Blake2RoundSpan.GLookups
public import Proven.NonVacuous.Blake2RoundSpan.ScheduleAsserts
public import Proven.NonVacuous.Blake2RoundSpan.Alignments
public import Proven.NonVacuous.Blake2RoundSpan.Timestamps0
public import Proven.NonVacuous.Blake2RoundSpan.Timestamps1
public import Proven.NonVacuous.Blake2RoundSpan.FinalLookups0
public import Proven.NonVacuous.Blake2RoundSpan.FinalLookups1
public import Proven.NonVacuous.Blake2RoundSpan.FinalLookups2
public import Proven.NonVacuous.Blake2RoundSpan.FinalLookups3
public import Proven.NonVacuous.Blake2RoundSpan.FinalLookups4
public import Proven.NonVacuous.Blake2RoundSpan.FinalLookups5
public import Proven.NonVacuous.Blake2RoundSpan.FinalLookups6
public import Proven.NonVacuous.Blake2RoundSpan.FinalLookups7
public import Proven.NonVacuous.Blake2RoundSpan.AssertsControl
public import Proven.NonVacuous.Blake2RoundSpan.AssertsProducts
public import Proven.NonVacuous.Blake2RoundSpan.AssertsChaining
public import Proven.NonVacuous.Blake2RoundSpan.AssertsLanes
public import Proven.NonVacuous.Blake2RoundSpan.AssertsWriteback
public import Proven.NonVacuous.Blake2RoundSpan.AssertsCarries
public import Proven.NonVacuous.Blake2RoundSpan.AssertsFinalBits
public import Proven.NonVacuous.Blake2RoundSpan.AssertsBorrowsLow
public import Proven.NonVacuous.Blake2RoundSpan.AssertsBorrowsHigh

@[expose] public section

/-! A round row's honest assignment of valid inputs satisfies its clock constraints (`Blake2Round.clockConstraints`
    over the exported setup, BabyBear): the 220 imported equations, the 194 imported queries (two pointer
    alignments, 128 G queries, 64 final-XOR queries) and the 89 timestamp queries, each block by its module. -/

namespace Airbender.NonVacuous.Blake2RoundSpan

variable {p : Nat} [Fact p.Prime]

/-- The schedule equations with the constraint list named. -/
private theorem schedule (x : RowInput) {L : List (Expression (ZMod p))}
    (hL : FlatOperation.constraints (Blake2Round.importedConstraints (p := p) Blake2Round.setupTable) = L) (n : Nat)
    (hn : n < L.length) (lower : 74 ≤ n) (upper : n ≤ 105) :
    (L.get ⟨n, hn⟩).eval (Verification.environment x.assignment) = 0 := by
  subst hL
  obtain ⟨j, limb, hj, hl, rfl⟩ : ∃ j limb, j < 16 ∧ limb < 2 ∧ n = 74 + 2 * j + limb :=
    ⟨(n - 74) / 2, (n - 74) % 2, by omega, by omega, by omega⟩
  exact schedule_asserts x Blake2Round.setupTable j hj limb hl

theorem asserts {x : RowInput} (valid : x.Valid) :
    ∀ i (h : i < (FlatOperation.constraints (Blake2Round.importedConstraints (p := p) Blake2Round.setupTable)).length),
      ((FlatOperation.constraints (Blake2Round.importedConstraints Blake2Round.setupTable)).get ⟨i, h⟩).eval
        (Verification.environment x.assignment) = 0 := by
  intro i h
  have size : i < 220 := by rwa [Blake2Round.constraint_count] at h
  generalize hL : FlatOperation.constraints (Blake2Round.importedConstraints (p := p) Blake2Round.setupTable) = L
    at h ⊢
  by_cases c0 : i ≤ 3
  · exact asserts_Control hL i h (Or.inl ⟨by omega, c0⟩)
  by_cases c1 : i ≤ 27
  · exact asserts_Chaining hL i h ⟨by omega, c1⟩
  by_cases c2 : i ≤ 51
  · exact asserts_Lanes hL i h ⟨by omega, c2⟩
  by_cases c3 : i ≤ 73
  · exact asserts_Products hL i h ⟨by omega, c3⟩
  by_cases c4 : i ≤ 105
  · exact schedule x hL i h (by omega) c4
  by_cases c5 : i ≤ 107
  · exact asserts_Control hL i h (Or.inr ⟨by omega, c5⟩)
  by_cases c6 : i ≤ 136
  · exact asserts_Writeback hL i h ⟨by omega, c6⟩
  by_cases c7 : i ≤ 160
  · exact asserts_Carries valid hL i h ⟨by omega, c7⟩
  by_cases c8 : i ≤ 176
  · exact asserts_FinalBits valid hL i h ⟨by omega, c8⟩
  by_cases c9 : i ≤ 197
  · exact asserts_BorrowsLow hL i h ⟨by omega, c9⟩
  · exact asserts_BorrowsHigh hL i h ⟨by omega, by omega⟩

theorem lookups (hp : p = 2013265921) {x : RowInput} (valid : x.Valid) :
    ∀ i (h : i < (FlatOperation.lookups (Blake2Round.importedConstraints (p := p) Blake2Round.setupTable)).length),
      ((FlatOperation.lookups (Blake2Round.importedConstraints Blake2Round.setupTable)).get ⟨i, h⟩).Contains
        (Verification.environment x.assignment) := by
  intro i h
  have size : i < 194 := by rwa [Blake2Round.lookup_count] at h
  generalize hL : FlatOperation.lookups (Blake2Round.importedConstraints (p := p) Blake2Round.setupTable) = L
    at h ⊢
  by_cases c0 : i ≤ 1
  · exact alignments hp valid hL i h c0
  by_cases c1 : i < 130
  · exact g_lookups hp valid hL i h (by omega) c1
  by_cases f0 : i < 138
  · exact final_lookups_0 hp valid hL i h (by omega) f0
  by_cases f1 : i < 146
  · exact final_lookups_1 hp valid hL i h (by omega) f1
  by_cases f2 : i < 154
  · exact final_lookups_2 hp valid hL i h (by omega) f2
  by_cases f3 : i < 162
  · exact final_lookups_3 hp valid hL i h (by omega) f3
  by_cases f4 : i < 170
  · exact final_lookups_4 hp valid hL i h (by omega) f4
  by_cases f5 : i < 178
  · exact final_lookups_5 hp valid hL i h (by omega) f5
  by_cases f6 : i < 186
  · exact final_lookups_6 hp valid hL i h (by omega) f6
  · exact final_lookups_7 hp valid hL i h (by omega) (by omega)

theorem timestamps (hp : p = 2013265921) {x : RowInput} (valid : x.Valid) :
    ∀ i (h : i < (FlatOperation.lookups (Blake2Round.importedConstraintsTimestampLookups (p := p))).length),
      ((FlatOperation.lookups (Blake2Round.importedConstraintsTimestampLookups (p := p))).get ⟨i, h⟩).Contains
        (Verification.environment x.assignment) := by
  intro i h
  have size : i < 89 := by rwa [Blake2Round.timestamp_count] at h
  generalize hL : FlatOperation.lookups (Blake2Round.importedConstraintsTimestampLookups (p := p)) = L at h ⊢
  by_cases c0 : i ≤ 44
  · exact timestamps_0 hp valid hL i h c0
  · exact timestamps_1 hp valid hL i h (by omega) (by omega)

/-- The honest assignment of valid inputs satisfies the round row's clock constraints over the exported setup. -/
theorem holds (hp : p = 2013265921) {x : RowInput} (valid : x.Valid) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment x.assignment)
      (Blake2Round.clockConstraints (Blake2Round.setupTable (p := p))) := by
  refine Verification.holds_append (holds_of_get (asserts valid) (lookups hp valid))
    (holds_of_get (fun i h => ?_) (timestamps hp valid))
  have empty : FlatOperation.constraints (Blake2Round.importedConstraintsTimestampLookups (p := p)) = [] := rfl
  rw [empty] at h
  exact absurd h (Nat.not_lt_zero i)

end Airbender.NonVacuous.Blake2RoundSpan
