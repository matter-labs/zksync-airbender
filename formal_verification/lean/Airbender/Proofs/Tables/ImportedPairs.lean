import Airbender.Review.Helpers.Tables.PairData

namespace Airbender.Verification.ImportedPairs
open Setup
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

private theorem affine_key (length n : Nat) (bound : n < length) :
    getFromBlocks [.affine length 0 1] n = some n := by
  simp [getFromBlocks, Block.get?, Block.length, bound]

private theorem affine_constant (length value n : Nat) (bound : n < length) :
    Block.get? (.affine length value 0) n = some value := by
  simp [Block.get?, Block.length, bound]

private theorem affine_unit (length first n : Nat) (bound : n < length) :
    Block.get? (.affine length first 1) n = some (first + n) := by
  simp [Block.get?, Block.length, bound]
  simpa only [Int.natCast_add] using
    And.intro (Int.natCast_nonneg (first + n)) (Int.toNat_natCast (first + n))

private theorem regZero_key (i : Fin 131072) :
    (regZeroData.columns[0]).get? i.val = some i.val := by
  exact affine_key 131072 i.val i.isLt

private theorem regZero_value (i : Fin 131072) :
    (regZeroData.columns[1]).get? i.val = some (if i.val = 0 then 1 else 0) := by
  change getFromBlocks [.dense (Array.replicate 1 1), .affine 131071 0 0] i.val = _
  by_cases zero : i.val = 0
  · simp [zero, getFromBlocks, Block.get?, Block.length]
  · have bound := i.isLt
    have tail : i.val - 1 < 131071 := by omega
    simp [getFromBlocks, Block.get?, Block.length, zero, tail]

/-- Exact key/value semantics of the actual imported zero-test region. -/
theorem regZero_row (i : Fin 131072) :
    setupPairRow regZeroData (by decide) i = (i.val, if i.val = 0 then 1 else 0) := by
  simp only [setupPairRow, show regZeroData.offset = 0 from rfl, Nat.zero_add,
    regZero_key i, regZero_value i, Option.getD_some]

private theorem sign_key (i : Fin 65536) :
    (signData.columns[0]).get? i.val = some i.val := by
  exact affine_key 65536 i.val i.isLt

private theorem sign_value (i : Fin 65536) :
    (signData.columns[1]).get? i.val = some (i.val / 32768) := by
  change getFromBlocks [.dense (Array.replicate 2 0),
    .affine 32766 0 0, .affine 32768 1 0] i.val = _
  have bound := i.isLt
  by_cases leading : i.val < 2
  · have value : i.val / 32768 = 0 := by omega
    simp [getFromBlocks, Block.get?, Block.length, leading, value]
  · by_cases lower : i.val < 32768
    · have value : i.val / 32768 = 0 := by omega
      have middle : i.val - 2 < 32766 := by omega
      simp [getFromBlocks, Block.get?, Block.length, leading, middle, value]
    · have value : i.val / 32768 = 1 := by omega
      have middle : ¬ i.val - 2 < 32766 := by omega
      have tail : i.val - 2 - 32766 < 32768 := by omega
      simp only [getFromBlocks, Block.length, Array.size_replicate,
        if_neg leading, if_neg middle, if_pos tail, value]
      exact affine_constant _ _ _ tail

/-- Exact key/sign semantics of the independently exported sign region. -/
theorem sign_row (i : Fin 65536) :
    setupPairRow signData (by decide) i = (i.val, i.val / 32768) := by
  simp only [setupPairRow, show signData.offset = 0 from rfl, Nat.zero_add,
    sign_key i, sign_value i, Option.getD_some]

private theorem periodic_cyclic_get (b count first n : Nat) (hb : 0 < b)
    (bound : n < count * b) :
    Block.get? (.periodic count 0 (Array.ofFn (fun i : Fin b =>
      (first + i.val) % b))) n = some ((first + n % b) % b) := by
  have hm : n % b < b := Nat.mod_lt _ hb
  simp [Block.get?, Block.length, bound, hm]
  simpa only [Int.natCast_emod, Int.natCast_add] using
    And.intro (Int.natCast_nonneg ((first + n) % b))
      (Int.toNat_natCast ((first + n) % b))

private theorem lowByte_key (i : Fin 65536) :
    (lowByteData.columns[0]).get? i.val = some i.val := by
  exact affine_key 65536 i.val i.isLt

private theorem lowByte_value (i : Fin 65536) :
    (lowByteData.columns[1]).get? i.val = some (i.val % 256) := by
  change getFromBlocks [.affine 1 0 0,
    .periodic 255 0 (Array.ofFn (fun i : Fin 256 => (1 + i.val) % 256)),
    .affine 255 1 1] i.val = _
  have bound := i.isLt
  by_cases zero : i.val = 0
  · simp [zero, getFromBlocks, Block.get?, Block.length]
  · by_cases middle : i.val < 65281
    · have period := periodic_cyclic_get 256 255 1 (i.val - 1) (by decide) (by omega)
      simp (disch := omega) only [getFromBlocks, Block.length, Array.size_ofFn,
        if_neg, if_pos, period]
      congr 1
      omega
    · have first : ¬ i.val < 1 := by omega
      have period : ¬ i.val - 1 < 65280 := by omega
      have tail : i.val - 1 - 65280 < 255 := by omega
      simp only [getFromBlocks, Block.length, Array.size_ofFn, Nat.reduceMul,
        if_neg first, if_neg period, if_pos tail]
      have value : 1 + (i.val - 1 - 65280) = i.val % 256 := by omega
      exact (affine_unit 255 1 _ tail).trans (congrArg some value)

/-- Exact low-byte semantics of the actual exported mul/div region. -/
theorem lowByte_row (i : Fin 65536) :
    setupPairRow lowByteData (by decide) i = (i.val, i.val % 256) := by
  simp only [setupPairRow, show lowByteData.offset = 0 from rfl, Nat.zero_add,
    lowByte_key i, lowByte_value i, Option.getD_some]

end Airbender.Verification.ImportedPairs
