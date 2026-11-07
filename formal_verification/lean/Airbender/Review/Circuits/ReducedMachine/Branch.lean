import Airbender.Review.Circuits.ReducedMachine.Comparison

namespace Airbender.ReducedMachine.Native
open Arithmetic Verification

/-- Actual rs2-use/branch/CONDITIONAL_COMMON_KEY mask. Original public branch
    decoding and architectural condition/target meaning remain separate. -/
def branchMask : Nat := 70

/-- Actual local branch routing, dummy third port and shared zero-test. These
    fields alone do not establish an original branch condition or target. -/
def BranchRouting (w : Nat → ZMod mersenne31Modulus) : Prop :=
  source2 w = #v[w 37,w 38] ∧
  (w 39 = w 6 ∧ w 40 = 0 ∧ w 88 = 1) ∧
  rdPort.address.code w = Nat.pair 0 (Nat.pair 0 0) ∧ rdWrite w = #v[0,0] ∧
  w 13 = w 66*w 69+(1-w 66)*w 49 ∧
  w 14 = w 66*w 70+(1-w 66)*w 50 ∧
  w 68 = if (w 61).val = 0 ∧ (w 62).val = 0 then 1 else 0

/-- Actual candidate target and decoded offset limbs, before PC selection. -/
def branchTargetWord (w : Nat → ZMod mersenne31Modulus) : Word := ⟨(w 69).val,(w 70).val⟩
def branchOffsetWord (w : Nat → ZMod mersenne31Modulus) : Word := ⟨(w 9).val,(w 10).val⟩

/-- The six original branch conditions, indexed by their native funct3.
    Public original decoding excludes the other tags. Sail execution is separate. -/
def branchCondition (tag : Nat) (left right : Word) : Bool :=
  match tag with
  | 0 => decide (left.toBitVec = right.toBitVec)
  | 1 => decide (left.toBitVec ≠ right.toBitVec)
  | 4 => decide (left.toBitVec.toInt < right.toBitVec.toInt)
  | 5 => decide (¬left.toBitVec.toInt < right.toBitVec.toInt)
  | 6 => decide (left.value < right.value)
  | 7 => decide (¬left.value < right.value)
  | _ => false


end Airbender.ReducedMachine.Native
