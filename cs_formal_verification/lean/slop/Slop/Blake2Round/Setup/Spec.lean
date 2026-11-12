module
public import Slop.Setup.Blocks

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

open Airbender.Import.Setup Airbender.Import.Setup.Proofs

abbrev col0Spec (n : Nat) : Int := Int.ofNat (spec0 n)
abbrev col1Spec (n : Nat) : Int := Int.ofNat (spec1 n)
abbrev col2Spec (n : Nat) : Int := Int.ofNat (spec2 n)
abbrev col3Spec (n : Nat) : Int := Int.ofNat (spec3 n)
abbrev col4Spec (n : Nat) : Int := Int.ofNat (spec4 n)
abbrev col5Spec (n : Nat) : Int := Int.ofNat (spec5 n)

/- Long blocks of each imported column, matched by shape: the import's grid blocks and the
   affine runs (every block of these columns). -/
def col0Longs : List (Nat × Shape) :=
  [(0, .grid 65536 (.digit 256 256)),
    (65536, .grid 16384 (.digit 128 128)),
    (81920, .grid 262144 (.digit 512 512)),
    (344064, .grid 196608 (.digit 256 256)),
    (540672, .grid 49152 (.digit 128 128)),
    (589824, .grid 16384 (.digit 1024 16)),
    (606208, .affine 442368 0 0)]

def col1Longs : List (Nat × Shape) :=
  [(0, .grid 65536 (.digit 1 256)),
    (65536, .grid 16384 (.digit 1 128)),
    (81920, .grid 262144 (.digit 1 512)),
    (344064, .grid 196608 (.digit 1 256)),
    (540672, .grid 49152 (.digit 1 128)),
    (589824, .grid 16384 (.digit 128 8)),
    (606208, .affine 442368 0 0)]

def col2Longs : List (Nat × Shape) :=
  [(0, .grid 65536 (.xorDigits 256 1 256)),
    (65536, .grid 16384 (.xorDigits 128 1 128)),
    (81920, .grid 262144 (.xorDigits 512 1 512)),
    (344064, .grid 196608 (.digit 65536 3)),
    (540672, .grid 49152 (.digit 16384 3)),
    (589824, .grid 16384 (.digit 8 16)),
    (606208, .affine 442368 0 0)]

def col3Longs : List (Nat × Shape) :=
  [(0, .affine 65536 0 0),
    (65536, .affine 16384 0 0),
    (81920, .affine 262144 0 0),
    (344064, .grid 196608 (.xorDigits 256 1 256)),
    (540672, .grid 49152 (.xorDigits 128 1 128)),
    (589824, .grid 16384 (.digit 1 8)),
    (606208, .affine 442368 0 0)]

def col4Longs : List (Nat × Shape) :=
  [(0, .affine 65536 0 0),
    (65536, .affine 16384 0 0),
    (81920, .affine 262144 0 0),
    (344064, .affine 196608 0 0),
    (540672, .affine 49152 0 0),
    (589824, .grid 16384 .xor4x3),
    (606208, .affine 442368 0 0)]

def col5Longs : List (Nat × Shape) :=
  [(0, .affine 65536 4 0),
    (65536, .affine 16384 19 0),
    (81920, .affine 262144 20 0),
    (344064, .affine 196608 55 0),
    (540672, .affine 49152 56 0),
    (589824, .affine 16384 57 0),
    (606208, .affine 442368 0 0)]

end Airbender.Blake2Round.SetupProofs
