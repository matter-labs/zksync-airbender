import Airbender.Import.SetupPacked
import Airbender.Proofs.Tables.PackedRunArithmetic

namespace Airbender.Setup.Proofs.PackedPayload
open PackedColumn PackedRun
set_option warningAsError true

theorem packedByte_eq (payload index : Nat) : packedByte payload index = digit payload index := by
  simp only [packedByte, digit, Nat.shiftRight_eq_div_pow]
  rw [pow_mul]
  norm_num

theorem packedArray_get (length payload index : Nat) (within : index < length) :
    (packedArray length payload)[index]'(by simpa [packedArray] using within) = digit payload index := by
  simp only [packedArray, Array.getElem_ofFn, packedByte_eq]

/-- The fixed-length byte decoder recovers exactly a bounded packed payload. -/
theorem payload_roundtrip (length payload : Nat) (bounded : payload < 256 ^ length) :
    Nat.ofDigits 256 (packedArray length payload).toList = payload := by
  let padded := Nat.digitsAppend 256 length payload
  have paddedLength : padded.length = length := Nat.length_digitsAppend (by omega) _ bounded
  have paddedValue : Nat.ofDigits 256 padded = payload := by
    simp [padded, Nat.digitsAppend, Nat.ofDigits_append_replicate_zero, Nat.ofDigits_digits]
  have same : (packedArray length payload).toList = padded := by
    apply List.ext_getElem
    · simpa [packedArray] using paddedLength.symm
    · intro index leftBound rightBound
      have raw := PackedBytes.extractDigit padded index
        (fun value member => Nat.lt_of_mem_digitsAppend (by omega) length value member) rightBound
      rw [paddedValue] at raw
      simpa only [Array.getElem_toList, packedArray, Array.getElem_ofFn, packedByte_eq, digit] using raw
  rw [same, paddedValue]

def _root_.Airbender.Setup.PackedRunInput.length (data : Setup.PackedRunInput) : Nat := data.count * data.period
def _root_.Airbender.Setup.PackedRunInput.asRun (data : Setup.PackedRunInput) : Run :=
  ⟨data.count, data.stride, packedArray data.period data.payload⟩
def _root_.Airbender.Setup.PackedRunInput.valid (data : Setup.PackedRunInput) : Bool :=
  data.payload < bytePower data.period &&
    (List.range data.period).all (fun index =>
      packedByte data.payload index + data.stride * (data.count - 1) < 256)
def _root_.Airbender.Setup.PackedRunInput.packed (data : Setup.PackedRunInput) : Nat :=
  if data.period = 0 then 0 else
  let standard := bytePower data.period
  let extent := bytePower data.length
  let geometric := (extent - 1) / (standard - 1)
  let moment := (data.count * extent + 1 - (geometric + extent)) / (standard - 1)
  data.payload * geometric + data.stride * ((standard - 1) / 255) * moment

theorem run_length (data : Setup.PackedRunInput) : data.asRun.length = data.length := by
  simp [PackedRunInput.asRun, Run.length, packedArray, PackedRunInput.length]

theorem valid_sound (data : Setup.PackedRunInput) (valid : data.valid = true) :
    data.asRun.valid = true := by
  simp only [PackedRunInput.valid, Bool.and_eq_true, decide_eq_true_eq] at valid
  apply Array.all_eq_true.mpr
  intro index within
  have indexBound : index < data.period := by simpa [PackedRunInput.asRun, packedArray] using within
  have entry := List.all_eq_true.mp valid.2 index (List.mem_range.mpr indexBound)
  simpa [PackedRunInput.asRun, packedArray, Run.valid] using entry

theorem packed_sound (data : Setup.PackedRunInput) (valid : data.valid = true) :
    data.packed = data.asRun.packedArithmetic := by
  have bound : data.payload < 256 ^ data.period := by
    have checked := valid
    simp only [PackedRunInput.valid, Bool.and_eq_true, decide_eq_true_eq, bytePower_eq] at checked
    exact checked.1
  simp only [PackedRunInput.packed, PackedRunInput.asRun, Run.packedArithmetic,
    packedArray, Array.size_ofFn, Run.length, PackedRunInput.length]
  rw [show Nat.ofDigits 256 (Array.ofFn (fun index : Fin data.period => packedByte data.payload index.val)).toList =
    data.payload from payload_roundtrip data.period data.payload bound]

end Airbender.Setup.Proofs.PackedPayload
