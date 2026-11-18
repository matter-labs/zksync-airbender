module
public import Human.ISA.ValidUse.Model
public import Mathlib.Data.BitVec
public import Mathlib.Tactic.Ring

@[expose] public section
namespace RV.ValidUse.BigintReferenceProofs
open Spec
set_option warningAsError true

/-- The bit-vector difference equals the low 256 bits of the bounded natural difference. -/
theorem subtraction (left right : BitVec 256) (carry : Bool) :
    BitVec.ofNat 256 (2 ^ 256 + left.toNat - (right.toNat + if carry then 1 else 0)) =
      left - right - (if carry then 1 else 0) := by
  have bounded : right.toNat + (if carry then 1 else 0) ≤ 2 ^ 256 + left.toNat := by
    have limit := right.isLt
    cases carry <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega
  change (((2 ^ 256 + left.toNat - (right.toNat + if carry then 1 else 0)) : Nat) : BitVec 256) = _
  rw [Nat.cast_sub bounded]
  simp only [Nat.cast_add]
  have modulus : ((2 ^ 256 : Nat) : BitVec 256) = 0 := by decide +kernel
  rw [modulus]
  simp only [zero_add]
  cases carry
  · simp
  · simpa using (sub_sub left right (1 : BitVec 256)).symm

/-- Concatenation gives the same little-endian value as the delegation word sum. -/
theorem decode_value (words : Vector Word 8) : (bigintValue words).toNat = Delegation.toU256 words := by
  simp only [bigintValue, BitVec.toNat_append]
  rw [← Nat.shiftLeft_add_eq_or_of_lt (words[0]).isLt,
    ← Nat.shiftLeft_add_eq_or_of_lt (words[1]).isLt,
    ← Nat.shiftLeft_add_eq_or_of_lt (words[2]).isLt,
    ← Nat.shiftLeft_add_eq_or_of_lt (words[3]).isLt,
    ← Nat.shiftLeft_add_eq_or_of_lt (words[4]).isLt,
    ← Nat.shiftLeft_add_eq_or_of_lt (words[5]).isLt,
    ← Nat.shiftLeft_add_eq_or_of_lt (words[6]).isLt]
  simp [Delegation.toU256, List.finRange_succ, Nat.shiftLeft_eq]
  ring

/-- Word extraction gives the same low words as natural division. -/
theorem encode_value (value : Nat) : bigintWords (BitVec.ofNat 256 value) = Delegation.ofU256 value := by
  apply Vector.ext
  intro index bound
  apply BitVec.eq_of_toNat_eq
  simp only [bigintWords, Delegation.ofU256, Vector.getElem_ofFn, BitVec.extractLsb'_toNat,
    BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  have offset : 32 * index + 32 ≤ 256 := by omega
  have factor : 2 ^ 256 = 2 ^ (32 * index) * 2 ^ (256 - 32 * index) := by
    rw [← pow_add]
    congr 1
    omega
  rw [factor, Nat.mod_mul_right_div_self]
  exact Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega))

/-- The product at twice the input width gives the unsigned high half without overflow. -/
theorem high_product (left right : BitVec width) :
    ((left.zeroExtend (width * 2)) * (right.zeroExtend (width * 2))).extractLsb' width width =
      BitVec.ofNat width (left.toNat * right.toNat / 2 ^ width) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.extractLsb'_toNat, BitVec.toNat_mul, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow, BitVec.zeroExtend, BitVec.toNat_setWidth_of_le (by omega : width ≤ width * 2)]
  rw [Nat.mod_eq_of_lt (BitVec.toNat_mul_toNat_lt (x := left) (y := right))]

/-- Each supported bit-vector operation has the delegation result and flag. -/
theorem operation_value (code : Word) (carry : Bool) (left right : BitVec 256)
    (supported : code.toNat ∈ [1, 2, 4, 8, 16, 32, 128]) :
    (Delegation.bigintOp code carry left.toNat right.toNat).map
        (fun result => (BitVec.ofNat 256 result.1, result.2)) =
      bigintOperation code.toNat carry left right := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at supported
  rcases supported with codeValue | codeValue | codeValue | codeValue | codeValue | codeValue | codeValue
  · simp only [Delegation.bigintOp, bigintOperation, codeValue, Option.map_some]
    cases carry <;> simp [BitVec.ofNat_add, BitVec.ofNat_toNat]
  · simp only [Delegation.bigintOp, bigintOperation, codeValue, Option.map_some]
    rw [subtraction left right carry]
    cases carry <;> simp
  · simp only [Delegation.bigintOp, bigintOperation, codeValue, Option.map_some]
    rw [subtraction right left carry]
    cases carry <;> simp
  · simp [Delegation.bigintOp, bigintOperation, codeValue, BitVec.ofNat_mul, BitVec.ofNat_toNat]
  · simp only [Delegation.bigintOp, bigintOperation, codeValue, Option.map_some]
    rw [high_product]
  · simp [Delegation.bigintOp, bigintOperation, codeValue, BitVec.ofNat_toNat]
  · simp only [Delegation.bigintOp, bigintOperation, codeValue, Option.map_some]
    cases carry <;> simp [BitVec.ofNat_add, BitVec.ofNat_toNat]

/-- All supported operations give the same result words and flag. -/
theorem words_operation_value (code : Word) (carry : Bool) (left right : Vector Word 8)
    (supported : code.toNat ∈ [1, 2, 4, 8, 16, 32, 128]) :
    (Delegation.bigintOp code carry (Delegation.toU256 left) (Delegation.toU256 right)).map
        (fun result => (Delegation.ofU256 result.1, result.2)) =
      (bigintOperation code.toNat carry (bigintValue left) (bigintValue right)).map
        (fun result => (bigintWords result.1, result.2)) := by
  have same := operation_value code carry (bigintValue left) (bigintValue right) supported
  have mapped := congrArg (Option.map (fun result : BitVec 256 × Bool => (bigintWords result.1, result.2))) same
  simpa only [Option.map_map, Function.comp_def, encode_value, decode_value] using mapped

end RV.ValidUse.BigintReferenceProofs
