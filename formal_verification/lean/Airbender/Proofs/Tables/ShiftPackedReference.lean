import Airbender.Proofs.Tables.ShiftOutputNormalization
import Airbender.Proofs.Tables.PackedWordColumn
import Airbender.Proofs.Tables.PackedDisjointSum

namespace Airbender.Verification.ShiftPackedReference
open Airbender.Setup.Proofs PackedSignedRun PackedWordBounds
set_option warningAsError true
set_option Elab.async false

/-- Keep all controls of the original native reference. -/
def rowByte (lane position byte control : Nat) : Nat :=
  ShiftCertificate.contributionNat position byte (control / 8 % 32) (control % 8) /
    256 ^ lane % 256

theorem contribution_or (position left right amount operation : Nat) :
    shiftByteContribution position (left ||| right) amount operation =
      shiftByteContribution position left amount operation |||
        shiftByteContribution position right amount operation := by
  have leftShift (x y : BitVec 32) (n : Nat) :
      (x ||| y).shiftLeft n = x.shiftLeft n ||| y.shiftLeft n :=
    BitVec.shiftLeft_or_distrib x y n
  unfold shiftByteContribution
  simp only [BitVec.ofNat_or]
  split
  · rw [leftShift, leftShift]
  · rw [leftShift]
    exact BitVec.ushiftRight_or_distrib _ _ _
  · rw [leftShift, BitVec.sshiftRight_or_distrib]
  · split_ifs
    · exact BitVec.shiftLeft_or_distrib _ _ _
    · rfl
  · rfl

theorem rowByte_or (lane position left right control : Nat) :
    rowByte lane position (left ||| right) control =
      rowByte lane position left control ||| rowByte lane position right control := by
  unfold rowByte
  simp only [← ShiftCertificate.contribution_toNat]
  rw [contribution_or, BitVec.toNat_or]
  have power : 256 ^ lane = 2 ^ (8 * lane) := by
    rw [show 256 = 2 ^ 8 from rfl, pow_mul]
  rw [power, Nat.or_div_two_pow]
  exact Nat.or_mod_two_pow (n := 8)

theorem rowByte_zero (lane position control : Nat) : rowByte lane position 0 control = 0 := by
  unfold rowByte ShiftCertificate.contributionNat
  split <;> simp_all

def wordFold (values : Nat → Nat) (byte : Nat) (bits : List Nat) : Nat :=
  bits.foldr (fun bit rest => (if byte.testBit bit then values bit else 0) ||| rest) 0

theorem byte_decomposition : ∀ byte : Fin 256,
    wordFold (fun bit => 2 ^ bit) byte.val (List.range 8) = byte.val := by decide +kernel

theorem wordFold_hom (function : Nat → Nat) (zero : function 0 = 0)
    (preserves : ∀ left right, function (left ||| right) = function left ||| function right)
    (values : Nat → Nat) (byte : Nat) (bits : List Nat) :
    function (wordFold values byte bits) = wordFold (fun bit => function (values bit)) byte bits := by
  induction bits with
  | nil => exact zero
  | cons bit rest ih =>
    simp only [wordFold, List.foldr_cons] at *
    rw [preserves, ih]
    cases byte.testBit bit <;> simp only [Bool.false_eq_true, ite_false, zero, ite_true]

theorem rowByte_decomposition (lane position byte control : Nat) (within : byte < 256) :
    rowByte lane position byte control =
      wordFold (fun bit => rowByte lane position (2 ^ bit) control) byte (List.range 8) := by
  calc
    rowByte lane position byte control =
        rowByte lane position (wordFold (fun bit => 2 ^ bit) byte (List.range 8)) control :=
      congrArg (fun value => rowByte lane position value control) (byte_decomposition ⟨byte, within⟩).symm
    _ = _ := wordFold_hom (fun value => rowByte lane position value control)
      (rowByte_zero lane position control) (fun left right => rowByte_or lane position left right control)
      _ _ _

theorem wordFold_digit (values : Nat → Nat) (byte : Nat) (bits : List Nat) (index : Nat) :
    digit 65536 (wordFold values byte bits) index =
      wordFold (fun bit => digit 65536 (values bit) index) byte bits := by
  induction bits with
  | nil => simp [wordFold, digit]
  | cons bit rest ih =>
    simp only [wordFold, List.foldr_cons] at *
    rw [extract_or, ih]
    cases byte.testBit bit <;> simp [digit]

def wordSum (values : Nat → Nat) (byte : Nat) (bits : List Nat) : Nat :=
  bits.foldr (fun bit rest => (if byte.testBit bit then values bit else 0) + rest) 0

theorem wordFold_disjoint (value : Nat) (values : Nat → Nat) (byte : Nat) (bits : List Nat)
    (disjoint : ∀ bit ∈ bits, value &&& values bit = 0) : value &&& wordFold values byte bits = 0 := by
  induction bits with
  | nil => simp [wordFold]
  | cons bit rest ih =>
    simp only [wordFold, List.foldr_cons] at *
    rw [Nat.and_or_distrib_left, ih (by intro index member; exact disjoint index (by simp [member]))]
    cases chosen : byte.testBit bit
    · simp
    · simp only [ite_true, disjoint bit (by simp), Nat.zero_or]

theorem wordFold_eq_sum (values : Nat → Nat) (byte : Nat) (bits : List Nat)
    (disjoint : bits.Pairwise (fun left right => values left &&& values right = 0)) :
    wordFold values byte bits = wordSum values byte bits := by
  induction bits with
  | nil => rfl
  | cons bit rest ih =>
    obtain ⟨first, tail⟩ := List.pairwise_cons.mp disjoint
    have separated := wordFold_disjoint (values bit) values byte rest first
    have sameTail := ih tail
    simp only [wordFold, wordSum, List.foldr_cons] at *
    cases chosen : byte.testBit bit
    · simpa using sameTail
    · simp only [ite_true]
      rw [PackedDisjointSum.disjoint_or _ _ separated, sameTail]

end Airbender.Verification.ShiftPackedReference
