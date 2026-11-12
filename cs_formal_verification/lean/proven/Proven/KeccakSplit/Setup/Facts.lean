module
public import Proven.KeccakSplit.Setup.Common
public import Human.Circuits.Keccak.Tables.Setup
public import Human.Helpers.Core.BabyBearPrime

@[expose] public section

/- Facts about the controller-row helpers and field casts shared by the three
   split Keccak setup membership proofs. -/

namespace Airbender.Keccak.Split.SetupProofs

set_option warningAsError true

theorem controlAt_lt {i : Nat} (h : i < 361) : controlAt i < 1600 := by
  unfold controlAt encode kindAt
  split_ifs <;> simp only [Kind.mode] <;> omega

/-- Distinct calls have distinct control words. -/
theorem controlAt_inj {a b : Nat} (ha : a < 361) (hb : b < 361)
    (h : controlAt a = controlAt b) : a = b := by
  unfold controlAt encode kindAt at h
  split_ifs at h <;> simp only [Kind.mode] at h <;> omega

theorem callIndex_lt {off j : Nat} (hoff : off ≤ 10) (hj : 1 ≤ j) (hj' : j ≤ 120) :
    callIndex off j < 361 := by
  unfold callIndex; omega

theorem parity_callIndex_lt {j : Nat} (hj : 1 ≤ j) (hj' : j ≤ 121) : callIndex 0 j < 361 := by
  unfold callIndex; omega

theorem parity_kindAt (j : Nat) :
    kindAt (callIndex 0 j) = .columnParity := by
  unfold kindAt callIndex
  split_ifs <;> first | rfl | omega

theorem thetaRho_kindAt (j : Nat) :
    kindAt (callIndex 5 j) = .thetaRho := by
  unfold kindAt callIndex
  split_ifs <;> first | rfl | omega

theorem chi5_kindAt (j : Nat) :
    kindAt (callIndex 10 j) = .chi5 := by
  unfold kindAt callIndex
  split_ifs <;> first | rfl | omega

theorem slotNat_eq {i pos : Nat} (hi : i < 361) (hp : pos < 7) :
    slotNat i pos = ((Call.slots ⟨i, hi⟩)[pos]).val := by
  simp only [slotNat, Call.slots, Vector.getElem_ofFn]
  split_ifs <;> rfl

theorem rcByte_eq_iotaByte : ∀ b < 256, rcByte b = Airbender.Keccak.iotaByte b := by
  decide +kernel

/-- A small natural keeps its value in the field. -/
theorem val_cast {v : Nat} (h : v < 2013265921) : ((v : ZMod babyBearModulus)).val = v :=
  ZMod.val_natCast_of_lt h

/-- Small naturals with equal casts are equal. -/
theorem cast_inj {a b : Nat} (ha : a < 2013265921) (hb : b < 2013265921)
    (h : (a : ZMod babyBearModulus) = (b : ZMod babyBearModulus)) : a = b := by
  have := congrArg ZMod.val h
  rwa [val_cast ha, val_cast hb] at this

theorem nib_lt (m k : Nat) : nib m k < 16 := Nat.mod_lt _ (by decide)

end Airbender.Keccak.Split.SetupProofs

namespace Airbender.Keccak.Split.SetupProofs

/-- Resolve the region `if`s of a row formula from bounds in context. -/
macro "region" : tactic => `(tactic| simp (disch := omega) only [ite_eq_left, ite_eq_right, ite_true, ite_false])

end Airbender.Keccak.Split.SetupProofs
