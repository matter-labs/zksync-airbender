import Airbender.Proofs.Tables.PackedWordBlocks

namespace Airbender.Setup.Proofs.PackedWordBounds
open PackedSignedRun PackedWordBlocks PackedRun
set_option warningAsError true

theorem extract_and (left right index : Nat) :
    digit 65536 (left &&& right) index = digit 65536 left index &&& digit 65536 right index := by
  have power : (65536 : Nat) ^ index = 2 ^ (16 * index) := by rw [pow_mul]; norm_num
  simp only [digit, power]
  rw [Nat.and_div_two_pow]
  simpa only [show (2 : Nat) ^ 16 = 65536 by norm_num] using
    (Nat.and_mod_two_pow (a := left / 2 ^ (16 * index)) (b := right / 2 ^ (16 * index)) (n := 16))

theorem extract_or (left right index : Nat) :
    digit 65536 (left ||| right) index = digit 65536 left index ||| digit 65536 right index := by
  have power : (65536 : Nat) ^ index = 2 ^ (16 * index) := by rw [pow_mul]; norm_num
  simp only [digit, power]
  rw [Nat.or_div_two_pow]
  simpa only [show (2 : Nat) ^ 16 = 65536 by norm_num] using
    (Nat.or_mod_two_pow (a := left / 2 ^ (16 * index)) (b := right / 2 ^ (16 * index)) (n := 16))

def units (count : Nat) : Nat := (65536 ^ count - 1) / 65535

theorem units_eq (count : Nat) : units count = ones 65536 count :=
  geometric_closed 65536 count (by omega)

theorem repeated_digit (value count index : Nat) (bounded : value < 65536) (within : index < count) :
    digit 65536 (value * units count) index = value := by
  rw [units_eq, ones, Nat.mul_ofDigits]
  simp only [List.map_replicate, mul_one]
  have result := PackedRadix.extractDigitBase 65536 (List.replicate count value) index (by omega)
    (fun entry member => (List.eq_of_mem_replicate member).symm ▸ bounded) (by simpa using within)
  simpa only [digit, List.getElem_replicate] using result

theorem translated_digits (radix : Nat) (values : List Nat) (shift : Nat) :
    Nat.ofDigits radix (values.map (fun value => value + shift)) =
      Nat.ofDigits radix values + shift * ones radix values.length := by
  induction values with
  | nil => simp [ones, Nat.ofDigits]
  | cons value rest ih =>
    simp only [List.map_cons, Nat.ofDigits, List.length_cons, ones,
      List.replicate_succ, Nat.cast_id] at *
    rw [ih]
    ring

theorem shifted_digit (payload count shift index : Nat) (bounded : payload < 65536 ^ count)
    (seeds : ∀ position < count, digit 65536 payload position < 512)
    (shiftBound : shift ≤ 32768) (within : index < count) :
    digit 65536 (payload + shift * units count) index = digit 65536 payload index + shift := by
  let values := (payloadArray 65536 count payload).toList
  have binding : Nat.ofDigits 65536 values = payload := payload_roundtrip 65536 count payload (by omega) bounded
  have length : values.length = count := by simp [values, payloadArray]
  have packed := translated_digits 65536 values shift
  rw [binding, length, ← units_eq] at packed
  rw [← packed]
  have bounds : ∀ value ∈ values.map (fun value => value + shift), value < 65536 := by
    intro value member
    obtain ⟨seed, seedMember, rfl⟩ := List.mem_map.mp member
    obtain ⟨position, positionBound, same⟩ := List.mem_iff_getElem.mp seedMember
    have positionWithin : position < count := by simpa [length] using positionBound
    have seedBound := seeds position positionWithin
    have seedValue : seed = digit 65536 payload position := by
      simpa [values, payloadArray] using same.symm
    omega
  have extracted := PackedRadix.extractDigitBase 65536 (values.map (fun value => value + shift)) index
    (by omega) bounds (by simpa [length] using within)
  simpa [digit, values, payloadArray] using extracted

def fastValid (data : Input) : Bool :=
  let delta := data.stride.natAbs * (data.count - 1)
  let repeated := units data.period
  decide (data.payload < 65536 ^ data.period ∧ delta < 512) &&
    (data.payload ||| (511 * repeated)) == 511 * repeated &&
    (if data.stride < 0 then
      (data.payload + (32768 - delta) * repeated) &&& (32768 * repeated) == 32768 * repeated
    else true)

theorem checkDigits_complete (radix : Nat) (predicate : Nat → Bool) (count payload : Nat)
    (holds : ∀ index < count, predicate (digit radix payload index) = true) :
    checkDigits radix predicate count payload = true := by
  induction count generalizing payload with
  | zero => rfl
  | succ count ih =>
    simp only [checkDigits, Bool.and_eq_true]
    constructor
    · simpa [digit] using holds 0 (by omega)
    · apply ih (payload / radix)
      intro index within
      have result := holds (index + 1) (by omega)
      simpa only [digit, pow_succ', Nat.div_div_eq_div_mul] using result

theorem fastValid_sound (data : Input) (checked : fastValid data = true) : data.valid 65536 = true := by
  simp only [fastValid, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at checked
  have bounded := checked.1.1.1
  have deltaBound := checked.1.1.2
  have seeds : ∀ index < data.period, digit 65536 data.payload index < 512 := by
    intro index within
    have result := congrArg (fun payload => digit 65536 payload index) checked.1.2
    rw [extract_or, repeated_digit 511 data.period index (by omega) within] at result
    have lower := (Nat.left_le_or : digit 65536 data.payload index ≤ digit 65536 data.payload index ||| 511)
    rw [result] at lower
    omega
  simp only [Input.valid, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨bounded, checkDigits_complete 65536 (data.seedValid 65536) data.period data.payload ?_⟩
  intro index within
  have seedBound := seeds index within
  have endpoint : 0 ≤ (digit 65536 data.payload index : Int) + data.stride * ((data.count - 1 : Nat) : Int) ∧
      (digit 65536 data.payload index : Int) + data.stride * ((data.count - 1 : Nat) : Int) < 65536 := by
    by_cases negative : data.stride < 0
    · have mask := checked.2
      simp only [if_pos negative, beq_iff_eq] at mask
      have result := congrArg (fun payload => digit 65536 payload index) mask
      rw [extract_and, repeated_digit 32768 data.period index (by omega) within,
        shifted_digit data.payload data.period (32768 - data.stride.natAbs * (data.count - 1)) index
          bounded seeds (by omega) within] at result
      have lower : ((digit 65536 data.payload index +
        (32768 - data.stride.natAbs * (data.count - 1))) &&& 32768) ≤
          digit 65536 data.payload index + (32768 - data.stride.natAbs * (data.count - 1)) := Nat.and_le_left
      rw [result] at lower
      have enough : data.stride.natAbs * (data.count - 1) ≤ digit 65536 data.payload index := by omega
      cases stride : data.stride with
      | ofNat step =>
        simp only [stride, Int.ofNat_eq_natCast] at negative
        omega
      | negSucc step =>
        simp only [stride, Int.natAbs_negSucc] at enough deltaBound
        have enoughInt : (((step + 1) * (data.count - 1) : Nat) : Int) ≤
            (digit 65536 data.payload index : Int) := by exact_mod_cast enough
        have product : Int.negSucc step * ((data.count - 1 : Nat) : Int) =
            -(((step + 1) * (data.count - 1) : Nat) : Int) := by
          push_cast
          rw [Int.negSucc_eq]
          ring
        rw [product]
        constructor <;> omega
    · have nonnegative : 0 ≤ data.stride := by omega
      cases stride : data.stride with
      | negSucc step => simp [stride] at nonnegative
      | ofNat step =>
        simp only [stride, Int.ofNat_eq_natCast, Int.natAbs_natCast] at deltaBound
        simp only [Int.ofNat_eq_natCast, ← Int.natCast_mul]
        constructor <;> omega
  simpa [Input.seedValid] using And.intro (by omega : digit 65536 data.payload index < 65536) endpoint

end Airbender.Setup.Proofs.PackedWordBounds
