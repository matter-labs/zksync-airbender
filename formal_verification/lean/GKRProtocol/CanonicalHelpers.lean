import GKRProtocol.HelperSemantics
import GKRProtocol.HelperAssertions

namespace Airbender.Compiler.Source
set_option warningAsError true

/-- Choose only compiler borrow witnesses; original columns and history values
are supplied independently and retained verbatim. -/
def canonicalHelpers (values : MemoryValues) (comparisons : List (MemoryWord × MemoryWord)) : HelperValues :=
  ⟨values, fun index => match comparisons[index]? with
    | none => 0
    | some (previous, current) => comparisonBorrow
        (previous.low.value values).val (current.low.value values).val⟩

theorem canonicalHelpers_boolean (values : MemoryValues) (comparisons : List (MemoryWord × MemoryWord)) (index : Nat) :
    let helpers := canonicalHelpers values comparisons
    helpers.borrow index * (helpers.borrow index - 1) = 0 := by
  cases found : comparisons[index]? with
  | none => simp only [canonicalHelpers, found, zero_mul]
  | some pair =>
      rcases pair with ⟨previous, current⟩
      have borrow : (canonicalHelpers values comparisons).borrow index =
          (comparisonBorrow (previous.low.value values).val (current.low.value values).val : BaseField) := by
        simp only [canonicalHelpers, found]
      change (canonicalHelpers values comparisons).borrow index *
        ((canonicalHelpers values comparisons).borrow index - 1) = 0
      rw [borrow]
      by_cases ordered : (previous.low.value values).val < (current.low.value values).val <;>
        simp [comparisonBorrow, ordered]

theorem canonicalHelpers_comparison (values : MemoryValues) (comparisons : List (MemoryWord × MemoryWord))
    {index : Nat} {previous current : MemoryWord} (found : comparisons[index]? = some (previous, current))
    (previousBound : (previous.timestamp values).Bounded) (currentBound : (current.timestamp values).Bounded)
    (ordered : (previous.timestamp values).value < (current.timestamp values).value) :
    let helpers := canonicalHelpers values comparisons
    (((comparisonFields previous current index).1).value helpers).val < 524288 ∧
      (((comparisonFields previous current index).2).value helpers).val < 524288 := by
  have complete := comparison_complete previousBound.1 previousBound.2 currentBound.1 currentBound.2 ordered
  dsimp only
  rw [comparisonFields_low, comparisonFields_high]
  simpa only [canonicalHelpers, found, MemoryWord.timestamp, ZMod.natCast_zmod_val] using complete.2

def clockCarry (initial final : MemoryWord) : HelperField :=
  .scale ((524288 : BaseField)⁻¹).val
    (.add (.add (.memory initial.low) (.memory (.constant 4))) (.neg (.memory final.low)))

def clockAssertions (initial final : MemoryWord) : List HelperAssertion :=
  [.boolean (clockCarry initial final),
   .zero (.add (.add (.memory final.high) (.neg (.memory initial.high))) (.neg (clockCarry initial final)))]

def borrowAssertions (count : Nat) : List HelperAssertion :=
  (List.range count).map (fun index => .boolean (.borrow index))

theorem borrowAssertions_complete (values : MemoryValues) (comparisons : List (MemoryWord × MemoryWord))
    (count : Nat) :
    ∀ assertion ∈ borrowAssertions count, assertion.value (canonicalHelpers values comparisons) = 0 := by
  intro assertion member
  obtain ⟨index, _, rfl⟩ := List.mem_map.mp member
  exact canonicalHelpers_boolean values comparisons index

theorem clockAssertions_complete (initial final : MemoryWord) (values : HelperValues)
    (initialBound : (initial.timestamp values.memory).Bounded) (finalBound : (final.timestamp values.memory).Bounded)
    (advance : (final.timestamp values.memory).value = (initial.timestamp values.memory).value + 4) :
    ∀ assertion ∈ clockAssertions initial final, assertion.value values = 0 := by
  have complete := clock_step_complete initialBound finalBound advance
  intro assertion member
  rcases List.mem_cons.mp member with same | tail
  · subst assertion
    simpa only [HelperAssertion.value, clockCarry, HelperField.value, MemoryField.value,
      MemoryWord.timestamp, ZMod.natCast_zmod_val, Nat.cast_ofNat, sub_eq_add_neg] using complete.1
  · have same := List.mem_singleton.mp tail
    subst assertion
    simpa only [HelperAssertion.value, clockCarry, HelperField.value, MemoryField.value,
      MemoryWord.timestamp, ZMod.natCast_zmod_val, Nat.cast_ofNat, sub_eq_add_neg] using complete.2

end Airbender.Compiler.Source
