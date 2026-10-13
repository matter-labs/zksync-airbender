import Airbender.Proofs.AddSub.ArtifactChecks
import Airbender.Review.Circuits.WordMemory.Artifact
import Airbender.Proofs.AddSub.Timestamp
import Airbender.Proofs.Trace.Timestamps

namespace Airbender.Trace.Proofs

theorem addSub_final_bound {p : Nat} [Fact p.Prime]
    {w : Nat → ZMod p} (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (AddSub.clockConstraints)) :
    (decodeTimestamp w AddSub.importedConstraintsTraceColumns.finalTime).Bounded := by
  have timestamps := Verification.holds_of_sublist h
    (List.sublist_append_right (AddSub.importedConstraints) (AddSub.importedConstraintsTimestampLookups))
  have lb := range_bound (Verification.lookup_of_holds timestamps
    ⟨0, by simp [AddSub.importedConstraintsTimestampLookups, FlatOperation.lookups]⟩)
  have hb := range_bound (Verification.lookup_of_holds timestamps
    ⟨1, by simp [AddSub.importedConstraintsTimestampLookups, FlatOperation.lookups]⟩)
  simp [Expression.eval, Verification.environment] at lb hb
  have finalBound : (decodeTimestamp w AddSub.importedConstraintsTraceColumns.finalTime).Bounded := ⟨lb, hb⟩
  exact finalBound

theorem addSub_step {p : Nat} [Fact p.Prime]
    (hp : 2 * timestampBase + 4 < p) (inverse : (-3840 : ZMod p) * 524288 = 1)
    {w : Nat → ZMod p} (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (AddSub.clockConstraints))
    (initialBound : (decodeTimestamp w AddSub.importedConstraintsTraceColumns.initialTime).Bounded) :
    (decodeTimestamp w AddSub.importedConstraintsTraceColumns.finalTime).Bounded ∧
      (decodeTimestamp w AddSub.importedConstraintsTraceColumns.finalTime).value =
        (decodeTimestamp w AddSub.importedConstraintsTraceColumns.initialTime).value + 4 := by
  have core := Verification.holds_of_sublist h
    (List.sublist_append_left (AddSub.importedConstraints) (AddSub.importedConstraintsTimestampLookups))
  have finalBound := addSub_final_bound h
  obtain ⟨carry, cb, low, high⟩ := AddSub.Proofs.timestamp_equations inverse core
  have advance := increment hp initialBound finalBound cb
    (by simpa [decodeTimestamp, AddSub.importedConstraintsTraceColumns,
      ZMod.natCast_zmod_val, timestampBase] using low)
    (by simpa [decodeTimestamp, AddSub.importedConstraintsTraceColumns,
      ZMod.natCast_zmod_val] using high)
  exact ⟨finalBound, advance⟩

theorem addSub_clock {p : Nat} [Fact p.Prime]
    (hp : 2 * timestampBase + 4 < p) (inverse : (-3840 : ZMod p) * 524288 = 1)
    {w : Nat → ZMod p} (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (AddSub.clockConstraints)) (inputs : ClockInputs AddSub.importedConstraintsTraceColumns w) :
    ClockEffects AddSub.importedConstraintsTraceColumns w := by
  have core := Verification.holds_of_sublist h
    (List.sublist_append_left (AddSub.importedConstraints) (AddSub.importedConstraintsTimestampLookups))
  have timestamps := Verification.holds_of_sublist h
    (List.sublist_append_right (AddSub.importedConstraints) (AddSub.importedConstraintsTimestampLookups))
  obtain ⟨finalBound, advance⟩ := addSub_step hp inverse h inputs.initial
  refine ⟨finalBound, advance, ?_⟩
  intro port member
  have previousBound := inputs.previous port member
  simp [AddSub.importedConstraintsTraceColumns] at member
  rcases member with rfl | rfl | rfl
  · have bit := Verification.assertion_of_holds core
      ⟨27, by simp [AddSub.importedConstraints, FlatOperation.constraints]⟩
    have lr := range_bound (Verification.lookup_of_holds timestamps
      ⟨2, by simp [AddSub.importedConstraintsTimestampLookups, FlatOperation.lookups]⟩)
    have hr := range_bound (Verification.lookup_of_holds timestamps
      ⟨3, by simp [AddSub.importedConstraintsTimestampLookups, FlatOperation.lookups]⟩)
    simp [Expression.eval, Verification.environment] at lr hr
    have normalized : w 42 * (w 42 - 1) = 0 := by
      simpa [AddSub.importedConstraints, FlatOperation.constraints, Expression.eval,
        Verification.environment, sub_eq_add_neg] using bit
    have lower : ((w 23 - w 2 - 0 + timestampBase * w 42) : ZMod p).val < timestampBase := by
      convert lr using 1; congr 1; ring
    have upper : ((w 24 + timestampBase - w 42 - w 3) : ZMod p).val < timestampBase := by
      convert hr using 1; congr 1; ring
    refine ⟨native_port_order hp inputs.initial previousBound (by decide) inputs.aligned normalized
      (by simpa [decodeTimestamp, AddSub.importedConstraintsTraceColumns,
        ZMod.natCast_zmod_val] using lower)
      (by simpa [decodeTimestamp, AddSub.importedConstraintsTraceColumns,
        ZMod.natCast_zmod_val] using upper), ?_⟩
    change (decodeTimestamp w AddSub.importedConstraintsTraceColumns.initialTime).value + 0 < _
    omega

  · have bit := Verification.assertion_of_holds core
      ⟨28, by simp [AddSub.importedConstraints, FlatOperation.constraints]⟩
    have lr := range_bound (Verification.lookup_of_holds timestamps
      ⟨4, by simp [AddSub.importedConstraintsTimestampLookups, FlatOperation.lookups]⟩)
    have hr := range_bound (Verification.lookup_of_holds timestamps
      ⟨5, by simp [AddSub.importedConstraintsTimestampLookups, FlatOperation.lookups]⟩)
    simp [Expression.eval, Verification.environment] at lr hr
    have normalized : w 43 * (w 43 - 1) = 0 := by
      simpa [AddSub.importedConstraints, FlatOperation.constraints, Expression.eval,
        Verification.environment, sub_eq_add_neg] using bit
    have lower : ((w 27 - w 2 - 1 + timestampBase * w 43) : ZMod p).val < timestampBase := by
      convert lr using 1; congr 1; ring
    have upper : ((w 28 + timestampBase - w 43 - w 3) : ZMod p).val < timestampBase := by
      convert hr using 1; congr 1; ring
    refine ⟨native_port_order hp inputs.initial previousBound (by decide) inputs.aligned normalized
      (by simpa [decodeTimestamp, AddSub.importedConstraintsTraceColumns,
        ZMod.natCast_zmod_val] using lower)
      (by simpa [decodeTimestamp, AddSub.importedConstraintsTraceColumns,
        ZMod.natCast_zmod_val] using upper), ?_⟩
    change (decodeTimestamp w AddSub.importedConstraintsTraceColumns.initialTime).value + 1 < _
    omega

  · have bit := Verification.assertion_of_holds core
      ⟨29, by simp [AddSub.importedConstraints, FlatOperation.constraints]⟩
    have lr := range_bound (Verification.lookup_of_holds timestamps
      ⟨6, by simp [AddSub.importedConstraintsTimestampLookups, FlatOperation.lookups]⟩)
    have hr := range_bound (Verification.lookup_of_holds timestamps
      ⟨7, by simp [AddSub.importedConstraintsTimestampLookups, FlatOperation.lookups]⟩)
    simp [Expression.eval, Verification.environment] at lr hr
    have normalized : w 44 * (w 44 - 1) = 0 := by
      simpa [AddSub.importedConstraints, FlatOperation.constraints, Expression.eval,
        Verification.environment, sub_eq_add_neg] using bit
    have lower : ((w 35 - w 2 - 2 + timestampBase * w 44) : ZMod p).val < timestampBase := by
      convert lr using 1; congr 1; ring
    have upper : ((w 36 + timestampBase - w 44 - w 3) : ZMod p).val < timestampBase := by
      convert hr using 1; congr 1; ring
    refine ⟨native_port_order hp inputs.initial previousBound (by decide) inputs.aligned normalized
      (by simpa [decodeTimestamp, AddSub.importedConstraintsTraceColumns,
        ZMod.natCast_zmod_val] using lower)
      (by simpa [decodeTimestamp, AddSub.importedConstraintsTraceColumns,
        ZMod.natCast_zmod_val] using upper), ?_⟩
    change (decodeTimestamp w AddSub.importedConstraintsTraceColumns.initialTime).value + 2 < _
    omega


theorem wordMemory_final_bound {p : Nat} [Fact p.Prime] (rom : Table (ZMod p) (fields 9))
    {w : Nat → ZMod p} (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (WordMemory.clockConstraints rom)) :
    (decodeTimestamp w WordMemory.importedConstraintsTraceColumns.finalTime).Bounded := by
  have timestamps := Verification.holds_of_sublist h
    (List.sublist_append_right (WordMemory.importedConstraints rom) (WordMemory.importedConstraintsTimestampLookups))
  have lb := range_bound (Verification.lookup_of_holds timestamps
    ⟨0, by simp [WordMemory.importedConstraintsTimestampLookups, FlatOperation.lookups]⟩)
  have hb := range_bound (Verification.lookup_of_holds timestamps
    ⟨1, by simp [WordMemory.importedConstraintsTimestampLookups, FlatOperation.lookups]⟩)
  simp [Expression.eval, Verification.environment] at lb hb
  have finalBound : (decodeTimestamp w WordMemory.importedConstraintsTraceColumns.finalTime).Bounded := ⟨lb, hb⟩
  exact finalBound

theorem wordMemory_step {p : Nat} [Fact p.Prime]
    (hp : 2 * timestampBase + 4 < p) (inverse : (-3840 : ZMod p) * 524288 = 1) (rom : Table (ZMod p) (fields 9))
    {w : Nat → ZMod p} (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (WordMemory.clockConstraints rom))
    (initialBound : (decodeTimestamp w WordMemory.importedConstraintsTraceColumns.initialTime).Bounded) :
    (decodeTimestamp w WordMemory.importedConstraintsTraceColumns.finalTime).Bounded ∧
      (decodeTimestamp w WordMemory.importedConstraintsTraceColumns.finalTime).value =
        (decodeTimestamp w WordMemory.importedConstraintsTraceColumns.initialTime).value + 4 := by
  have core := Verification.holds_of_sublist h
    (List.sublist_append_left (WordMemory.importedConstraints rom) (WordMemory.importedConstraintsTimestampLookups))
  have finalBound := wordMemory_final_bound rom h
  have boolean := Verification.assertion_of_holds core
    ⟨20, by simp [WordMemory.importedConstraints, FlatOperation.constraints]⟩
  have high := Verification.assertion_of_holds core
    ⟨21, by simp [WordMemory.importedConstraints, FlatOperation.constraints]⟩
  simp [WordMemory.importedConstraints, FlatOperation.constraints, Expression.eval, Verification.environment] at boolean high
  have bit : (-3840 * (w 2 + 4 - w 13)) * (-3840 * (w 2 + 4 - w 13) - 1) = 0 := by
    convert boolean using 1
    ring
  have eq : -3840 * (w 2 + 4 - w 13) + w 3 - w 14 = 0 := by
    linear_combination -high
  obtain ⟨carry, cb, low, high⟩ := Arithmetic.increment_carry inverse bit eq
  have advance := increment hp initialBound finalBound cb
    (by simpa [decodeTimestamp, WordMemory.importedConstraintsTraceColumns,
      ZMod.natCast_zmod_val, timestampBase] using low)
    (by simpa [decodeTimestamp, WordMemory.importedConstraintsTraceColumns,
      ZMod.natCast_zmod_val] using high)
  exact ⟨finalBound, advance⟩

theorem wordMemory_clock {p : Nat} [Fact p.Prime]
    (hp : 2 * timestampBase + 4 < p) (inverse : (-3840 : ZMod p) * 524288 = 1) (rom : Table (ZMod p) (fields 9))
    {w : Nat → ZMod p} (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (WordMemory.clockConstraints rom)) (inputs : ClockInputs WordMemory.importedConstraintsTraceColumns w) :
    ClockEffects WordMemory.importedConstraintsTraceColumns w := by
  have core := Verification.holds_of_sublist h
    (List.sublist_append_left (WordMemory.importedConstraints rom) (WordMemory.importedConstraintsTimestampLookups))
  have timestamps := Verification.holds_of_sublist h
    (List.sublist_append_right (WordMemory.importedConstraints rom) (WordMemory.importedConstraintsTimestampLookups))
  obtain ⟨finalBound, advance⟩ := wordMemory_step hp inverse rom h inputs.initial
  refine ⟨finalBound, advance, ?_⟩
  intro port member
  have previousBound := inputs.previous port member
  simp [WordMemory.importedConstraintsTraceColumns] at member
  rcases member with rfl | rfl | rfl
  · have bit := Verification.assertion_of_holds core
      ⟨24, by simp [WordMemory.importedConstraints, FlatOperation.constraints]⟩
    have lr := range_bound (Verification.lookup_of_holds timestamps
      ⟨2, by simp [WordMemory.importedConstraintsTimestampLookups, FlatOperation.lookups]⟩)
    have hr := range_bound (Verification.lookup_of_holds timestamps
      ⟨3, by simp [WordMemory.importedConstraintsTimestampLookups, FlatOperation.lookups]⟩)
    simp [Expression.eval, Verification.environment] at lr hr
    have normalized : w 46 * (w 46 - 1) = 0 := by
      simpa [WordMemory.importedConstraints, FlatOperation.constraints, Expression.eval,
        Verification.environment, sub_eq_add_neg] using bit
    have lower : ((w 15 - w 2 - 0 + timestampBase * w 46) : ZMod p).val < timestampBase := by
      convert lr using 1; congr 1; ring
    have upper : ((w 16 + timestampBase - w 46 - w 3) : ZMod p).val < timestampBase := by
      convert hr using 1; congr 1; ring
    refine ⟨native_port_order hp inputs.initial previousBound (by decide) inputs.aligned normalized
      (by simpa [decodeTimestamp, WordMemory.importedConstraintsTraceColumns,
        ZMod.natCast_zmod_val] using lower)
      (by simpa [decodeTimestamp, WordMemory.importedConstraintsTraceColumns,
        ZMod.natCast_zmod_val] using upper), ?_⟩
    change (decodeTimestamp w WordMemory.importedConstraintsTraceColumns.initialTime).value + 0 < _
    omega

  · have bit := Verification.assertion_of_holds core
      ⟨25, by simp [WordMemory.importedConstraints, FlatOperation.constraints]⟩
    have lr := range_bound (Verification.lookup_of_holds timestamps
      ⟨4, by simp [WordMemory.importedConstraintsTimestampLookups, FlatOperation.lookups]⟩)
    have hr := range_bound (Verification.lookup_of_holds timestamps
      ⟨5, by simp [WordMemory.importedConstraintsTimestampLookups, FlatOperation.lookups]⟩)
    simp [Expression.eval, Verification.environment] at lr hr
    have normalized : w 47 * (w 47 - 1) = 0 := by
      simpa [WordMemory.importedConstraints, FlatOperation.constraints, Expression.eval,
        Verification.environment, sub_eq_add_neg] using bit
    have lower : ((w 21 - w 2 - 1 + timestampBase * w 47) : ZMod p).val < timestampBase := by
      convert lr using 1; congr 1; ring
    have upper : ((w 22 + timestampBase - w 47 - w 3) : ZMod p).val < timestampBase := by
      convert hr using 1; congr 1; ring
    refine ⟨native_port_order hp inputs.initial previousBound (by decide) inputs.aligned normalized
      (by simpa [decodeTimestamp, WordMemory.importedConstraintsTraceColumns,
        ZMod.natCast_zmod_val] using lower)
      (by simpa [decodeTimestamp, WordMemory.importedConstraintsTraceColumns,
        ZMod.natCast_zmod_val] using upper), ?_⟩
    change (decodeTimestamp w WordMemory.importedConstraintsTraceColumns.initialTime).value + 1 < _
    omega

  · have bit := Verification.assertion_of_holds core
      ⟨26, by simp [WordMemory.importedConstraints, FlatOperation.constraints]⟩
    have lr := range_bound (Verification.lookup_of_holds timestamps
      ⟨6, by simp [WordMemory.importedConstraintsTimestampLookups, FlatOperation.lookups]⟩)
    have hr := range_bound (Verification.lookup_of_holds timestamps
      ⟨7, by simp [WordMemory.importedConstraintsTimestampLookups, FlatOperation.lookups]⟩)
    simp [Expression.eval, Verification.environment] at lr hr
    have normalized : w 48 * (w 48 - 1) = 0 := by
      simpa [WordMemory.importedConstraints, FlatOperation.constraints, Expression.eval,
        Verification.environment, sub_eq_add_neg] using bit
    have lower : ((w 27 - w 2 - 2 + timestampBase * w 48) : ZMod p).val < timestampBase := by
      convert lr using 1; congr 1; ring
    have upper : ((w 28 + timestampBase - w 48 - w 3) : ZMod p).val < timestampBase := by
      convert hr using 1; congr 1; ring
    refine ⟨native_port_order hp inputs.initial previousBound (by decide) inputs.aligned normalized
      (by simpa [decodeTimestamp, WordMemory.importedConstraintsTraceColumns,
        ZMod.natCast_zmod_val] using lower)
      (by simpa [decodeTimestamp, WordMemory.importedConstraintsTraceColumns,
        ZMod.natCast_zmod_val] using upper), ?_⟩
    change (decodeTimestamp w WordMemory.importedConstraintsTraceColumns.initialTime).value + 2 < _
    omega


end Airbender.Trace.Proofs
