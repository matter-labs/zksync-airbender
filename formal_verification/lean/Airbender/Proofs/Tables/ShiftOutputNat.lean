import Airbender.Proofs.Tables.ShiftOutputBase

namespace Airbender.Verification.ShiftCertificate
set_option warningAsError true
set_option Elab.async false

/-- Arithmetic evaluation of the unchanged bit-vector reference, including invalid controls. -/
def contributionNat (position byte amount operation : Nat) : Nat :=
  let input := ((byte % 4294967296) <<< (8 * position)) % 4294967296
  match operation with
  | 1 => (input <<< amount) % 4294967296
  | 2 => input >>> amount
  | 3 => if 2147483648 ≤ input then
      4294967295 - ((4294967295 - input) >>> amount) else input >>> amount
  | 5 => if amount = 0 then
      ((byte % 4294967296) <<< (8 * (3 - position))) % 4294967296 else 0
  | _ => 0

private theorem left_nat (x : BitVec 32) (n : Nat) :
    (x.shiftLeft n).toNat = (x.toNat <<< n) % 4294967296 := rfl

private theorem right_nat (x : BitVec 32) (n : Nat) :
    (x.ushiftRight n).toNat = x.toNat >>> n := rfl

theorem contribution_toNat (position byte amount operation : Nat) :
    (shiftByteContribution position byte amount operation).toNat =
      contributionNat position byte amount operation := by
  unfold shiftByteContribution contributionNat
  split
  all_goals simp only [left_nat, right_nat, BitVec.toNat_ofNat,
    BitVec.toNat_sshiftRight, BitVec.msb_eq_decide, decide_eq_true_eq,
    Nat.reducePow, Nat.reduceSub]
  all_goals first | rfl | (split_ifs <;> rfl)

end Airbender.Verification.ShiftCertificate
