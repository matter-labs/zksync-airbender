import Human.Circuits.Blake2Round.SetupArtifact
import Slop.Setup.Blocks

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

open Airbender.Import.Setup.Proofs

abbrev col0Spec (n : Nat) : Int := Int.ofNat (spec0 n)

def col0Longs : List (Nat × Shape) :=
  [(0, .periodic 256 1 256), (65536, .periodic 128 1 128), (81920, .periodic 512 1 512), (344064, .periodic 256 1 256), (409600, .periodic 256 1 256), (475136, .periodic 256 1 256), (540672, .periodic 128 1 128), (557056, .periodic 128 1 128), (573440, .periodic 128 1 128), (589824, .periodic 16 1 1024), (606208, .affine 442368 0 0)]


abbrev col1Spec (n : Nat) : Int := Int.ofNat (spec1 n)

def col1Longs : List (Nat × Shape) :=
  [(0, .periodic 256 0 256), (65536, .periodic 129 0 128), (82048, .periodic 512 0 512), (344192, .periodic 768 0 256), (540800, .periodic 383 0 128), (589824, .periodic 16 0 1024), (606208, .affine 442368 0 0)]


abbrev col2Spec (n : Nat) : Int := Int.ofNat (spec2 n)

def col2Longs : List (Nat × Shape) :=
  [(344064, .affine 65536 0 0), (409600, .affine 65536 1 0), (475136, .affine 65536 2 0), (540672, .affine 16384 0 0), (557056, .affine 16384 1 0), (573440, .affine 16384 2 0), (589824, .periodic 128 0 128), (606208, .affine 442368 0 0)]


abbrev col3Spec (n : Nat) : Int := Int.ofNat (spec3 n)

def col3Longs : List (Nat × Shape) :=
  [(0, .affine 344065 0 0), (589824, .periodic 2048 0 8), (606208, .affine 442368 0 0)]


abbrev col4Spec (n : Nat) : Int := Int.ofNat (spec4 n)

def col4Longs : List (Nat × Shape) :=
  [(0, .affine 589825 0 0), (606208, .affine 442368 0 0)]


abbrev col5Spec (n : Nat) : Int := Int.ofNat (spec5 n)

def col5Longs : List (Nat × Shape) :=
  [(0, .affine 65536 4 0), (65536, .affine 16384 19 0), (81920, .affine 262144 20 0), (344064, .affine 196608 55 0), (540672, .affine 49152 56 0), (589824, .affine 16384 57 0), (606208, .affine 442368 0 0)]

end Airbender.Blake2Round.SetupProofs
