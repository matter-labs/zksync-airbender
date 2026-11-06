import Airbender.Review.Circuits.ReducedMachine.ShiftContributions

namespace Airbender.ReducedMachine.NativeShiftNaturalProofs
open Native NativeFixed Verification
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

-- Internal calculations only. Initialized read induction must derive the bounds.
def keyNat (mode : ShiftMode) (limb amount : Nat) : Nat :=
  limb + 65536 * amount + 2097152 * (if mode = .left then 0 else 1)

def outputs (mode : ShiftMode) (limb amount : Nat) : Vector Nat 2 :=
  if mode = .left then #v[(limb * 2 ^ amount) % 65536,(limb * 2 ^ amount / 65536) % 65536]
  else #v[limb / 2 ^ amount,(limb * 65536 / 2 ^ amount) % 65536]

def assembledLow (mode : ShiftMode) (lo hi amount : Nat) : Nat :=
  if mode = .left then (lo * 2 ^ amount) % 65536
  else lo / 2 ^ amount + (hi * 65536 / 2 ^ amount) % 65536 + mode.filler hi amount % 65536

def assembledHigh (mode : ShiftMode) (lo hi amount : Nat) : Nat :=
  if mode = .left then (hi * 2 ^ amount) % 65536 + (lo * 2 ^ amount / 65536) % 65536
  else hi / 2 ^ amount + mode.filler hi amount / 65536

/-- Natural packing stays below22bits and retains exact limb/amount/direction fields. -/
theorem key_fields (mode : ShiftMode) (limb amount : Nat)
    (source : limb < 65536) (small : amount < 32) :
    keyNat mode limb amount < 4194304 ∧
      keyNat mode limb amount % 65536 = limb ∧
      keyNat mode limb amount / 65536 = amount + 32 * (if mode = .left then 0 else 1) := by
  cases mode <;> simp [keyNat] <;> omega

/-- No Mersenne31 rollover in bounded source/amount packing. -/
theorem canonical_key (mode : ShiftMode) (limb amount : ZMod mersenne31Modulus)
    (source : limb.val < 65536) (small : amount.val < 32) :
    (mode.lookupKey limb amount).val = keyNat mode limb.val amount.val := by
  have bound := (key_fields mode limb.val amount.val source small).1
  have field : (keyNat mode limb.val amount.val : ZMod mersenne31Modulus) = mode.lookupKey limb amount := by
    cases mode <;> simp [keyNat,ShiftMode.lookupKey,Nat.cast_add,Nat.cast_mul ]
  have natural := congrArg ZMod.val field
  rw [ZMod.val_natCast_of_lt (by change keyNat mode limb.val amount.val < 2147483647; omega)] at natural
  exact natural.symm

/-- Interpret the actual monolithic row at the exact bounded source key. -/
theorem packed_outputs (mode : ShiftMode) (limb amount : Nat)
    (source : limb < 65536) (small : amount < 32) :
    shiftOutputs (keyNat mode limb amount) = outputs mode limb amount := by
  have rem : (limb + 65536 * amount) % 65536 = limb := by omega
  have quot : (limb + 65536 * amount) / 65536 = amount := by omega
  have lower : limb + 65536 * amount < 2097152 := by omega
  cases mode
  · change shiftOutputs (limb + 65536 * amount) =
      #v[(limb * 2 ^ amount) % 65536,(limb * 2 ^ amount / 65536) % 65536]
    rw [shiftOutputs,if_pos lower]
    exact congrArg₂ (fun a b : Nat => #v[a,b])
      (by simp only [sllHighOutput,rem,quot])
      (by simp only [sllLowHighOutput,rem,quot])
  all_goals
    change shiftOutputs (limb + 65536 * amount + 2097152) =
      #v[limb / 2 ^ amount,(limb * 65536 / 2 ^ amount) % 65536]
    rw [shiftOutputs,if_neg (by omega)]
    have sub : limb + 65536 * amount + 2097152 - 2097152 = limb + 65536 * amount := by omega
    exact (congrArg (fun n => #v[srlLowOutput n,srlHighLowOutput n]) sub).trans
      (congrArg₂ (fun a b : Nat => #v[a,b])
        (by simp only [srlLowOutput,rem,quot])
        (by simp only [srlHighLowOutput,rem,quot]))

end Airbender.ReducedMachine.NativeShiftNaturalProofs
