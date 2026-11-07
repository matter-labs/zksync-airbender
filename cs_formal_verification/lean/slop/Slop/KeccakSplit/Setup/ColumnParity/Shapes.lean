import Slop.KeccakSplit.Setup.ColumnParity.Spec

/- Long blocks of each imported column, matched by shape: the import's grid blocks and the
   affine runs longer than 200 rows (the other blocks are checked row by row in `Rows`). -/

namespace Airbender.Keccak.Split.ColumnParity.SetupProofs

open Airbender.Import.Setup Airbender.Import.Setup.Proofs

set_option warningAsError true

/-- The iota table's per-byte constants, as the import emitted them. -/
def iotaTable : Array Nat :=
  #[0, 1, 130, 138, 0, 139, 1, 129, 9, 138, 136, 9, 10, 139, 139, 137, 3, 2, 128, 10, 10, 129, 128, 1, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 128, 128, 128, 128, 0, 128, 128, 0, 0, 128, 0, 128, 0, 128, 128, 128, 0, 128, 0, 128, 128, 0, 128, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 128, 0, 128, 128, 0, 0, 0, 128, 128, 128, 0, 0, 0, 0, 0, 0, 128, 128, 0, 128, 128, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 128, 128, 0, 0, 128, 128, 0, 0, 0, 0, 0, 128, 128, 128, 128, 128, 0, 128, 128, 128, 0, 128, 0, 0, 0, 0, 0, 0, 0]

abbrev col0Spec (n : Nat) : Int := Int.ofNat (spec0 n)

def col0Longs : List (Nat × Shape) :=
  [(0, .grid 65536 (.digit 1 256)),
    (65780, .grid 1048576 (.digit 1 16)),
    (1114356, .affine 3079948 0 0)]

abbrev col1Spec (n : Nat) : Int := Int.ofNat (spec1 n)

def col1Longs : List (Nat × Shape) :=
  [(0, .grid 65536 (.digit 256 256)),
    (65780, .grid 1048576 (.digit 16 16)),
    (1114356, .affine 3079948 0 0)]

abbrev col2Spec (n : Nat) : Int := Int.ofNat (spec2 n)

def col2Longs : List (Nat × Shape) :=
  [(0, .grid 65536 (.xorTable 256 iotaTable)),
    (65780, .grid 1048576 (.digit 256 16)),
    (1114356, .affine 3079948 0 0)]

abbrev col3Spec (n : Nat) : Int := Int.ofNat (spec3 n)

def col3Longs : List (Nat × Shape) :=
  [(0, .affine 65536 0 0),
    (65780, .grid 1048576 (.digit 4096 16)),
    (1114356, .affine 3079948 0 0)]

abbrev col4Spec (n : Nat) : Int := Int.ofNat (spec4 n)

def col4Longs : List (Nat × Shape) :=
  [(0, .affine 65536 0 0),
    (65780, .grid 1048576 (.digit 65536 16)),
    (1114356, .affine 3079948 0 0)]

abbrev col5Spec (n : Nat) : Int := Int.ofNat (spec5 n)

def col5Longs : List (Nat × Shape) :=
  [(0, .affine 65536 0 0),
    (65780, .grid 1048576 .xor5),
    (1114356, .affine 3079948 0 0)]

abbrev col6Spec (n : Nat) : Int := Int.ofNat (spec6 n)

def col6Longs : List (Nat × Shape) :=
  [(0, .affine 65536 0 0),
    (65780, .affine 1048576 0 0),
    (1114356, .affine 3079948 0 0)]

abbrev col7Spec (n : Nat) : Int := Int.ofNat (spec7 n)

def col7Longs : List (Nat × Shape) :=
  [(0, .affine 65536 38 0),
    (65780, .affine 1048576 64 0),
    (1114356, .affine 3079948 0 0)]

end Airbender.Keccak.Split.ColumnParity.SetupProofs
