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

end Airbender.ReducedMachine.Native
