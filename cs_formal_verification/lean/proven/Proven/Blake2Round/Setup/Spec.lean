module
public import Proven.Setup.Blocks

@[expose] public section

/- Row formulas of the six exported setup columns (cs/src/tables/binops.rs:
   create_xor_table, create_xor_with_carry_table, create_xor_4x3_table), one
   function per column; rows from 606208 on are padding (all zero). -/

namespace Airbender.Blake2Round.SetupProofs

def spec0 (n : Nat) : Nat :=
  if n < 65536 then n / 256
  else if n < 81920 then (n - 65536) / 128
  else if n < 344064 then (n - 81920) / 512
  else if n < 540672 then (n - 344064) % 65536 / 256
  else if n < 589824 then (n - 540672) % 16384 / 128
  else if n < 606208 then (n - 589824) / 1024
  else 0

def spec1 (n : Nat) : Nat :=
  if n < 65536 then n % 256
  else if n < 81920 then (n - 65536) % 128
  else if n < 344064 then (n - 81920) % 512
  else if n < 540672 then (n - 344064) % 256
  else if n < 589824 then (n - 540672) % 128
  else if n < 606208 then (n - 589824) / 128 % 8
  else 0

def spec2 (n : Nat) : Nat :=
  if n < 65536 then n / 256 ^^^ n % 256
  else if n < 81920 then (n - 65536) / 128 ^^^ (n - 65536) % 128
  else if n < 344064 then (n - 81920) / 512 ^^^ (n - 81920) % 512
  else if n < 540672 then (n - 344064) / 65536
  else if n < 589824 then (n - 540672) / 16384
  else if n < 606208 then (n - 589824) / 8 % 16
  else 0

def spec3 (n : Nat) : Nat :=
  if n < 344064 then 0
  else if n < 540672 then (n - 344064) % 65536 / 256 ^^^ (n - 344064) % 256
  else if n < 589824 then (n - 540672) % 16384 / 128 ^^^ (n - 540672) % 128
  else if n < 606208 then (n - 589824) % 8
  else 0

def spec4 (n : Nat) : Nat :=
  if n < 589824 then 0
  else if n < 606208 then
    ((n - 589824) / 1024 ^^^ (n - 589824) / 8 % 16) |||
      (((n - 589824) / 128 % 8 ^^^ (n - 589824) % 8) <<< 4)
  else 0

def spec5 (n : Nat) : Nat :=
  if n < 65536 then 4
  else if n < 81920 then 19
  else if n < 344064 then 20
  else if n < 540672 then 55
  else if n < 589824 then 56
  else if n < 606208 then 57
  else 0

abbrev col0Spec (n : Nat) : Int := Int.ofNat (spec0 n)
abbrev col1Spec (n : Nat) : Int := Int.ofNat (spec1 n)
abbrev col2Spec (n : Nat) : Int := Int.ofNat (spec2 n)
abbrev col3Spec (n : Nat) : Int := Int.ofNat (spec3 n)
abbrev col4Spec (n : Nat) : Int := Int.ofNat (spec4 n)
abbrev col5Spec (n : Nat) : Int := Int.ofNat (spec5 n)

end Airbender.Blake2Round.SetupProofs
