module
public import Human.Compiler.NativeSetups.Rows
public import Proven.Setup.Scan

@[expose] public section

/- Shared pieces of the fast column formulas of the CPU setups: the stored form of the field element `-1`, one bit of
   a key, and the ROM words of the setup fixture program. -/

namespace Airbender.Compiler.NativeSetups.Proofs
open Airbender.Import.Setup.Scan

/-- The field element `-1`, as the native setup stores it. -/
abbrev sentinel : Nat := 2013265920

/-- Bit `place` of `key`, as 0 or 1. -/
def bit (key place : Nat) : Nat := Nat.mod (Nat.div key place) 2

/-- `fixtureWords`, as natural numbers. -/
def word (key : Nat) : Nat :=
  pick (Nat.beq key 0) 19 <| pick (Nat.beq key 1) 4227219 <| pick (Nat.beq key 2) 111 <|
    pick (Nat.beq key 3) 7438771 0

theorem word_eq (key : Nat) : (fixtureWords key).toNat = word key := by
  rcases key with _ | _ | _ | _ | key <;> simp [fixtureWords, word, nat_beq]

end Airbender.Compiler.NativeSetups.Proofs
