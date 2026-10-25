import GKRProtocol.CanonicalHelpers

namespace Airbender.Compiler.Source
set_option warningAsError true

inductive HelperClock where
  | executor : MemoryWord → HelperClock
  | worker : MemoryWord → MemoryField → HelperClock

def HelperClock.fields : HelperClock → List HelperField
  | .executor final => [.memory final.low, .memory final.high]
  | .worker invocation execute => [.scale ((4 : BaseField)⁻¹).val
      (.add (.memory invocation.low) (.neg (.memory execute)))]

/-- Integer clock data, independent of the compiler's inverse-power query. -/
def HelperClock.Valid (values : MemoryValues) : HelperClock → Prop
  | .executor final => (final.timestamp values).Bounded
  | .worker invocation execute => ∃ slot : Nat, slot < 131072 ∧
      invocation.low.value values = (4 : BaseField) * slot + execute.value values

theorem HelperClock.fields_valid (clock : HelperClock) (values : HelperValues)
    (valid : clock.Valid values.memory) :
    ∀ field ∈ clock.fields, (field.value values).val < 524288 := by
  cases clock with
  | executor final =>
      intro field member
      rcases List.mem_cons.mp member with rfl | tail
      · exact valid.1
      · have same := List.mem_singleton.mp tail
        subst field
        exact valid.2
  | worker invocation execute =>
      obtain ⟨slot, bounded, equation⟩ := valid
      intro field member
      have same := List.mem_singleton.mp member
      subst field
      change (((((4 : BaseField)⁻¹).val : BaseField) *
        (invocation.low.value values.memory + -execute.value values.memory)).val) < 524288
      rw [ZMod.natCast_zmod_val, equation]
      have nonzero : (4 : BaseField) ≠ 0 := by decide +kernel
      have simplify : (4 : BaseField)⁻¹ * (4 * slot + execute.value values.memory +
          -execute.value values.memory) = slot := by
        rw [add_neg_cancel_right, ← mul_assoc, inv_mul_cancel₀ nonzero, one_mul]
      rw [simplify, ZMod.val_natCast_of_lt (lt_trans bounded (by decide : 131072 < babyBearModulus))]
      omega

structure HelperAlignment where
  scale : Nat
  pointer : MemoryField

def HelperAlignment.field (alignment : HelperAlignment) : HelperField :=
  .scale (((alignment.scale : BaseField)⁻¹).val) (.memory alignment.pointer)

def HelperAlignment.Valid (alignment : HelperAlignment) (values : MemoryValues) : Prop :=
  0 < alignment.scale ∧ alignment.scale * 524288 < babyBearModulus ∧
    (alignment.pointer.value values).val < 65536 ∧ alignment.scale ∣ (alignment.pointer.value values).val

theorem HelperAlignment.field_valid (alignment : HelperAlignment) (values : HelperValues)
    (valid : alignment.Valid values.memory) : (alignment.field.value values).val < 524288 := by
  simpa only [field, HelperField.value, ZMod.natCast_zmod_val] using
    alignment_complete valid.1 valid.2.1 valid.2.2.1 valid.2.2.2

structure HelperProfile where
  clock : HelperClock
  comparisons : List (MemoryWord × MemoryWord)
  alignments : List HelperAlignment

def HelperProfile.fields (profile : HelperProfile) : List HelperField :=
  profile.clock.fields ++
    profile.comparisons.zipIdx.flatMap (fun (pair, index) =>
      [ (comparisonFields pair.1 pair.2 index).1, (comparisonFields pair.1 pair.2 index).2 ]) ++
    profile.alignments.map HelperAlignment.field

/-- Source primitive conditions: ordinary integer order, clock phase, and
address alignment. No native helper query or lookup equation is a premise. -/
structure HelperProfile.Valid (profile : HelperProfile) (values : MemoryValues) : Prop where
  clock : profile.clock.Valid values
  comparisons : ∀ pair ∈ profile.comparisons,
    (pair.1.timestamp values).Bounded ∧ (pair.2.timestamp values).Bounded ∧
      (pair.1.timestamp values).value < (pair.2.timestamp values).value
  alignments : ∀ alignment ∈ profile.alignments, alignment.Valid values

theorem HelperProfile.canonical_fields_valid (profile : HelperProfile) (values : MemoryValues)
    (valid : profile.Valid values) :
    ∀ field ∈ profile.fields,
      (field.value (canonicalHelpers values profile.comparisons)).val < 524288 := by
  intro field member
  rcases List.mem_append.mp member with head | alignmentMember
  · rcases List.mem_append.mp head with clockMember | comparisonMember
    · exact profile.clock.fields_valid _ valid.clock field clockMember
    · obtain ⟨⟨pair, index⟩, included, fieldMember⟩ := List.mem_flatMap.mp comparisonMember
      have found : profile.comparisons[index]? = some pair :=
        List.mk_mem_zipIdx_iff_getElem?.mp included
      have pairMember : pair ∈ profile.comparisons := List.mem_of_getElem? found
      have ordered := valid.comparisons pair pairMember
      have ranges := canonicalHelpers_comparison values profile.comparisons found
        ordered.1 ordered.2.1 ordered.2.2
      rcases List.mem_cons.mp fieldMember with same | tail
      · subst field; exact ranges.1
      · have same := List.mem_singleton.mp tail
        subst field; exact ranges.2
  · obtain ⟨alignment, included, rfl⟩ := List.mem_map.mp alignmentMember
    exact alignment.field_valid _ (valid.alignments alignment included)

def HelperClock.protectedFields : HelperClock → List MemoryField
  | .executor final => [final.low, final.high]
  | .worker invocation execute => [invocation.low, execute]

theorem HelperClock.valid_congr (clock : HelperClock) (before after : MemoryValues)
    (same : ∀ field ∈ clock.protectedFields, field.value after = field.value before)
    (valid : clock.Valid before) : clock.Valid after := by
  cases clock with
  | executor final =>
      change (final.low.value after).val < 524288 ∧ (final.high.value after).val < 524288
      rw [same final.low (by simp [protectedFields]), same final.high (by simp [protectedFields])]
      exact valid
  | worker invocation execute =>
      change ∃ slot : Nat, slot < 131072 ∧ invocation.low.value after = 4 * slot + execute.value after
      rw [same invocation.low (by simp [protectedFields]), same execute (by simp [protectedFields])]
      exact valid

def HelperProfile.protectedFields (profile : HelperProfile) : List MemoryField :=
  profile.clock.protectedFields ++ profile.comparisons.flatMap (fun pair => [pair.2.low, pair.2.high]) ++
    profile.alignments.map HelperAlignment.pointer

/-- Active histories satisfy the source RAM order. Padding histories are
existential witnesses; positivity permits choosing zero for them. -/
structure HelperProfile.ExecutionValid (profile : HelperProfile) (execute : BaseField)
    (values : MemoryValues) : Prop where
  clock : profile.clock.Valid values
  current : ∀ pair ∈ profile.comparisons, (pair.2.timestamp values).Bounded
  active : execute ≠ 0 → ∀ pair ∈ profile.comparisons,
    (pair.1.timestamp values).Bounded ∧ (pair.1.timestamp values).value < (pair.2.timestamp values).value
  inactive : execute = 0 → ∀ pair ∈ profile.comparisons, 0 < (pair.2.timestamp values).value
  alignments : ∀ alignment ∈ profile.alignments, alignment.Valid values

theorem HelperProfile.canonicalized_valid (profile : HelperProfile) (execute : BaseField)
    (before after : MemoryValues) (valid : profile.ExecutionValid execute before)
    (same : ∀ field ∈ profile.protectedFields, field.value after = field.value before)
    (active : execute ≠ 0 → ∀ pair ∈ profile.comparisons, pair.1.timestamp after = pair.1.timestamp before)
    (inactive : execute = 0 → ∀ pair ∈ profile.comparisons,
      pair.1.low.value after = 0 ∧ pair.1.high.value after = 0) : profile.Valid after := by
  have currentSame (pair : MemoryWord × MemoryWord) (member : pair ∈ profile.comparisons) :
      pair.2.timestamp after = pair.2.timestamp before := by
    have low := same pair.2.low (List.mem_append_left _ (List.mem_append_right _
      (List.mem_flatMap.mpr ⟨pair, member, by simp⟩)))
    have high := same pair.2.high (List.mem_append_left _ (List.mem_append_right _
      (List.mem_flatMap.mpr ⟨pair, member, by simp⟩)))
    simp only [MemoryWord.timestamp, low, high]
  refine ⟨profile.clock.valid_congr before after (fun field member =>
    same field (List.mem_append_left _ (List.mem_append_left _ member))) valid.clock, ?_, ?_⟩
  · intro pair member
    rw [currentSame pair member]
    refine ⟨?_, valid.current pair member, ?_⟩
    · by_cases zero : execute = 0
      · have erased := inactive zero pair member
        change (pair.1.low.value after).val < 524288 ∧ (pair.1.high.value after).val < 524288
        rw [erased.1, erased.2]
        decide
      · rw [active zero pair member]
        exact (valid.active zero pair member).1
    · by_cases zero : execute = 0
      · have erased := inactive zero pair member
        have positive := valid.inactive zero pair member
        simpa only [MemoryWord.timestamp, Trace.Timestamp.value, erased.1, erased.2,
          ZMod.val_zero, Nat.mul_zero, Nat.zero_add] using positive
      · rw [active zero pair member]
        exact (valid.active zero pair member).2
  · intro alignment member
    have pointerSame := same alignment.pointer
      (List.mem_append_right _ (List.mem_map.mpr ⟨alignment, member, rfl⟩))
    unfold HelperAlignment.Valid
    rw [pointerSame]
    exact valid.alignments alignment member

end Airbender.Compiler.Source
