import GKRProtocol.HelperSource
import Airbender.Proofs.Trace.Timestamps
import Airbender.Proofs.BabyBear

namespace Airbender.Compiler
set_option warningAsError true

def Source.MemoryWord.timestamp (word : Source.MemoryWord) (values : Source.MemoryValues) : Trace.Timestamp :=
  ⟨(word.low.value values).val, (word.high.value values).val⟩

theorem comparisonFields_low (previous current : Source.MemoryWord) (index : Nat) (values : Source.HelperValues) :
    ((Source.comparisonFields previous current index).1).value values =
      previous.low.value values.memory - current.low.value values.memory + 524288 * values.borrow index := by
  simp only [Source.comparisonFields, Source.HelperField.value]
  ring

theorem comparisonFields_high (previous current : Source.MemoryWord) (index : Nat) (values : Source.HelperValues) :
    ((Source.comparisonFields previous current index).2).value values =
      previous.high.value values.memory + 524288 - values.borrow index - current.high.value values.memory := by
  simp only [Source.comparisonFields, Source.HelperField.value, Source.MemoryField.value]
  ring

/-- Actual two-limb borrowed range queries imply strict order in the source
clock domain. The full 38-bit timestamp need not fit into BabyBear. -/
theorem comparison_sound (previous current : Source.MemoryWord) (index : Nat) (values : Source.HelperValues)
    (previousBound : (previous.timestamp values.memory).Bounded)
    (currentBound : (current.timestamp values.memory).Bounded)
    (bit : values.borrow index * (values.borrow index - 1) = 0)
    (low : (((Source.comparisonFields previous current index).1).value values).val < 524288)
    (high : (((Source.comparisonFields previous current index).2).value values).val < 524288) :
    (previous.timestamp values.memory).value < (current.timestamp values.memory).value := by
  rw [comparisonFields_low] at low
  rw [comparisonFields_high] at high
  have ordered := Trace.Proofs.native_port_order_of_room (p := babyBearModulus) (by decide)
    currentBound previousBound (offset := 0) (by decide) currentBound.1 bit
    (by simpa [Source.MemoryWord.timestamp, Trace.timestampBase] using low)
    (by simpa [Source.MemoryWord.timestamp, Trace.timestampBase] using high)
  simpa only [Nat.add_zero] using ordered

def comparisonBorrow (previousLow currentLow : Nat) : Nat := if previousLow < currentLow then 1 else 0

/-- Construct the compiler's Boolean borrow from independent integer clock
order. No compiled range or helper assertion is a premise. -/
theorem comparison_complete {previousLow previousHigh currentLow currentHigh : Nat}
    (previousLowBound : previousLow < 524288) (previousHighBound : previousHigh < 524288)
    (currentLowBound : currentLow < 524288) (currentHighBound : currentHigh < 524288)
    (ordered : previousLow + 524288 * previousHigh < currentLow + 524288 * currentHigh) :
    let borrow : Source.BaseField := comparisonBorrow previousLow currentLow
    borrow * (borrow - 1) = 0 ∧
      ((previousLow : Source.BaseField) - currentLow + 524288 * borrow).val < 524288 ∧
      ((previousHigh : Source.BaseField) + 524288 - borrow - currentHigh).val < 524288 := by
  let carry := comparisonBorrow previousLow currentLow
  have carryCases : carry = 0 ∨ carry = 1 := by
    dsimp [carry, comparisonBorrow]
    split <;> simp
  have nonnegative : currentLow ≤ previousLow + 524288 * carry := by
    dsimp [carry, comparisonBorrow]
    split <;> omega
  let low := previousLow + 524288 * carry - currentLow
  let high := previousHigh + 524288 - carry - currentHigh
  have lowEquation : low + currentLow = previousLow + 524288 * carry := Nat.sub_add_cancel nonnegative
  have highEquation : high + carry + currentHigh = previousHigh + 524288 := by
    dsimp [high]
    rcases carryCases with h | h <;> rw [h] <;> omega
  have lowBound : low < 524288 := by
    dsimp [low, carry, comparisonBorrow]
    split <;> omega
  have highBound : high < 524288 := by
    dsimp [high, carry, comparisonBorrow]
    split <;> omega
  have lowField : (previousLow : Source.BaseField) - currentLow + 524288 * (carry : Source.BaseField) = low := by
    have equation : (low : Source.BaseField) + currentLow = previousLow + 524288 * (carry : Source.BaseField) := by
      simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using
        congrArg (fun n : Nat => (n : Source.BaseField)) lowEquation
    linear_combination -equation
  have highField : (previousHigh : Source.BaseField) + 524288 - (carry : Source.BaseField) - currentHigh = high := by
    have equation : (high : Source.BaseField) + (carry : Source.BaseField) + currentHigh = previousHigh + 524288 := by
      simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using
        congrArg (fun n : Nat => (n : Source.BaseField)) highEquation
    linear_combination -equation
  change (carry : Source.BaseField) * ((carry : Source.BaseField) - 1) = 0 ∧ _
  refine ⟨?_, ?_, ?_⟩
  · rcases carryCases with h | h <;> simp [h]
  · rw [lowField, ZMod.val_natCast_of_lt (show low < babyBearModulus from lt_trans lowBound (by decide))]
    exact lowBound
  · rw [highField, ZMod.val_natCast_of_lt (show high < babyBearModulus from lt_trans highBound (by decide))]
    exact highBound

/-- The compiler's inverse-power range check enforces integer alignment when
the checked field-capacity bound holds. -/
theorem alignment_sound {scale : Nat} (positive : 0 < scale) (capacity : scale * 524288 < babyBearModulus)
    {pointer : Source.BaseField}
    (ranged : (((scale : Source.BaseField)⁻¹ * pointer).val) < 524288) :
    scale ∣ pointer.val := by
  let quotient : Source.BaseField := (scale : Source.BaseField)⁻¹ * pointer
  have scaleBound : scale < babyBearModulus := by omega
  have nonzero : (scale : Source.BaseField) ≠ 0 := by
    intro zero
    have vals := congrArg ZMod.val zero
    rw [ZMod.val_natCast_of_lt scaleBound] at vals
    have : scale = 0 := by simpa using vals
    omega
  have equation : (scale * quotient.val : Nat) = pointer.val := by
    apply Arithmetic.bounded_nat_eq (F := Source.BaseField) (p := babyBearModulus)
    · exact lt_trans (Nat.mul_lt_mul_of_pos_left ranged positive) capacity
    · exact ZMod.val_lt pointer
    · simp only [Nat.cast_mul, ZMod.natCast_zmod_val]
      dsimp [quotient]
      rw [← mul_assoc, mul_inv_cancel₀ nonzero, one_mul]
  exact ⟨quotient.val, equation.symm⟩

theorem alignment_complete {scale : Nat} (positive : 0 < scale) (capacity : scale * 524288 < babyBearModulus)
    {pointer : Source.BaseField} (pointerBound : pointer.val < 65536) (aligned : scale ∣ pointer.val) :
    (((scale : Source.BaseField)⁻¹ * pointer).val) < 524288 := by
  obtain ⟨quotient, equation⟩ := aligned
  have quotientBound : quotient < 524288 := by nlinarith
  have scaleBound : scale < babyBearModulus := by omega
  have nonzero : (scale : Source.BaseField) ≠ 0 := by
    intro zero
    have vals := congrArg ZMod.val zero
    rw [ZMod.val_natCast_of_lt scaleBound] at vals
    have : scale = 0 := by simpa using vals
    omega
  have field : pointer = (scale : Source.BaseField) * quotient := by
    have cast := congrArg (fun n : Nat => (n : Source.BaseField)) equation
    simpa only [ZMod.natCast_zmod_val, Nat.cast_mul] using cast
  rw [field, ← mul_assoc, inv_mul_cancel₀ nonzero, one_mul,
    ZMod.val_natCast_of_lt (show quotient < babyBearModulus from lt_trans quotientBound (by decide))]
  exact quotientBound

/-- The extra executor arithmetic assertions are consequences of ordinary
integer clock advance, rather than new assumptions on a source witness. -/
theorem clock_step_complete {initial final : Trace.Timestamp}
    (initialBound : initial.Bounded) (finalBound : final.Bounded)
    (advance : final.value = initial.value + 4) :
    let carry : Source.BaseField := (524288 : Source.BaseField)⁻¹ *
      ((initial.lo : Source.BaseField) + 4 - final.lo)
    carry * (carry - 1) = 0 ∧ (final.hi : Source.BaseField) - initial.hi - carry = 0 := by
  let carry : Nat := if initial.lo + 4 < 524288 then 0 else 1
  have carryCases : carry = 0 ∨ carry = 1 := by dsimp [carry]; split <;> simp
  have low : initial.lo + 4 = final.lo + 524288 * carry := by
    rcases initialBound with ⟨il, ih⟩
    rcases finalBound with ⟨fl, fh⟩
    dsimp [Trace.Timestamp.value, Trace.timestampBase] at advance il ih fl fh
    dsimp [carry]
    split <;> omega
  have high : initial.hi + carry = final.hi := by
    rcases initialBound with ⟨il, ih⟩
    rcases finalBound with ⟨fl, fh⟩
    dsimp [Trace.Timestamp.value, Trace.timestampBase] at advance il ih fl fh
    rcases carryCases with h | h <;> rw [h] at low ⊢ <;> omega
  have inverse : (524288 : Source.BaseField) ≠ 0 := by decide +kernel
  have recovered : (524288 : Source.BaseField)⁻¹ * ((initial.lo : Source.BaseField) + 4 - final.lo) = carry := by
    have field : (initial.lo : Source.BaseField) + 4 = final.lo + 524288 * (carry : Source.BaseField) := by
      simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using
        congrArg (fun n : Nat => (n : Source.BaseField)) low
    rw [show (initial.lo : Source.BaseField) + 4 - final.lo = 524288 * (carry : Source.BaseField) by
      linear_combination field]
    rw [← mul_assoc, inv_mul_cancel₀ inverse, one_mul]
  dsimp only
  rw [recovered]
  refine ⟨?_, ?_⟩
  · rcases carryCases with h | h <;> simp [h]
  · have field : (initial.hi : Source.BaseField) + (carry : Source.BaseField) = final.hi := by
      simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using
        congrArg (fun n : Nat => (n : Source.BaseField)) high
    linear_combination -field

/-- The actual delegation quotient fixes the invocation clock's low two bits,
without assuming a compiled clock congruence. -/
theorem invocation_clock_sound (execute low : Source.BaseField)
    (bit : execute * (execute - 1) = 0)
    (ranged : (((4 : Source.BaseField)⁻¹ * (low - execute)).val) < 524288) :
    low.val % 4 = execute.val := by
  obtain ⟨active, activeBound, activeEquation⟩ := Arithmetic.boolean_nat bit
  let quotient : Source.BaseField := (4 : Source.BaseField)⁻¹ * (low - execute)
  have quotientBound : quotient.val < 524288 := ranged
  have nonzero : (4 : Source.BaseField) ≠ 0 := by decide +kernel
  have field : ((4 * quotient.val + active : Nat) : Source.BaseField) = low := by
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, ZMod.natCast_zmod_val]
    rw [← activeEquation]
    dsimp [quotient]
    rw [← mul_assoc, mul_inv_cancel₀ nonzero, one_mul]
    ring
  have natural : 4 * quotient.val + active = low.val :=
    Arithmetic.bounded_nat_eq (F := Source.BaseField) (p := babyBearModulus)
      (by change 4 * quotient.val + active < 2013265921; omega) (ZMod.val_lt low)
      (by simpa only [ZMod.natCast_zmod_val] using field)
  have activeValue : execute.val = active := by
    rw [activeEquation, ZMod.val_natCast_of_lt (show active < babyBearModulus by
      change active < 2013265921; omega)]
  rw [activeValue]
  omega

theorem invocation_clock_complete (execute low : Source.BaseField) (bounded : low.val < 524288)
    (clockShape : low.val % 4 = execute.val) :
    (((4 : Source.BaseField)⁻¹ * (low - execute)).val) < 524288 := by
  let quotient := low.val / 4
  have quotientBound : quotient < 524288 := lt_of_le_of_lt (Nat.div_le_self _ _) bounded
  have natural : execute.val + 4 * quotient = low.val := by
    simpa only [← clockShape] using Nat.mod_add_div low.val 4
  have field : execute + 4 * (quotient : Source.BaseField) = low := by
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, ZMod.natCast_zmod_val] using
      congrArg (fun n : Nat => (n : Source.BaseField)) natural
  have nonzero : (4 : Source.BaseField) ≠ 0 := by decide +kernel
  have recovered : (4 : Source.BaseField)⁻¹ * (low - execute) = quotient := by
    rw [show low - execute = 4 * (quotient : Source.BaseField) by linear_combination -field]
    rw [← mul_assoc, inv_mul_cancel₀ nonzero, one_mul]
  rw [recovered, ZMod.val_natCast_of_lt (show quotient < babyBearModulus from lt_trans quotientBound (by decide))]
  exact quotientBound

end Airbender.Compiler
