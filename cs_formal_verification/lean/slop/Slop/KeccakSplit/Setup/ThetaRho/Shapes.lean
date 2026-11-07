import Slop.KeccakSplit.Setup.ThetaRho.Spec

/- Long blocks of each imported column, matched by shape: the import's grid blocks and the
   affine runs longer than 200 rows (the other blocks are checked row by row in `Rows`). -/

namespace Airbender.Keccak.Split.ThetaRho.SetupProofs

open Airbender.Import.Setup Airbender.Import.Setup.Proofs

set_option warningAsError true

abbrev col0Spec (n : Nat) : Int := Int.ofNat (spec0 n)

def col0Longs : List (Nat × Shape) :=
  [(0, .grid 65536 (.digit 256 256)),
    (65536, .grid 524288 (.digit 1 256)),
    (590066, .affine 3604238 0 0)]

abbrev col1Spec (n : Nat) : Int := Int.ofNat (spec1 n)

def col1Longs : List (Nat × Shape) :=
  [(0, .grid 65536 (.digit 1 256)),
    (65536, .grid 524288 (.digit 256 256)),
    (590066, .affine 3604238 0 0)]

abbrev col2Spec (n : Nat) : Int := Int.ofNat (spec2 n)

def col2Longs : List (Nat × Shape) :=
  [(0, .grid 65536 (.xorDigits 256 1 256)),
    (65536, .grid 524288 (.digit 65536 8)),
    (590066, .affine 3604238 0 0)]

abbrev col3Spec (n : Nat) : Int := Int.ofNat (spec3 n)

def col3Longs : List (Nat × Shape) :=
  [(0, .affine 65536 0 0),
    (65536, .grid 524288 .rotLow),
    (590066, .affine 3604238 0 0)]

abbrev col4Spec (n : Nat) : Int := Int.ofNat (spec4 n)

def col4Longs : List (Nat × Shape) :=
  [(0, .affine 65536 0 0),
    (65536, .grid 524288 .rotHigh),
    (590066, .affine 3604238 0 0)]

abbrev col5Spec (n : Nat) : Int := Int.ofNat (spec5 n)

def col5Longs : List (Nat × Shape) :=
  [(0, .affine 65536 0 0),
    (65536, .affine 524288 0 0),
    (590066, .affine 3604238 0 0)]

abbrev col6Spec (n : Nat) : Int := Int.ofNat (spec6 n)

def col6Longs : List (Nat × Shape) :=
  [(0, .affine 65536 0 0),
    (65536, .affine 524288 0 0),
    (590066, .affine 3604238 0 0)]

abbrev col7Spec (n : Nat) : Int := Int.ofNat (spec7 n)

def col7Longs : List (Nat × Shape) :=
  [(0, .affine 65536 0 0),
    (65536, .affine 524288 0 0),
    (590066, .affine 3604238 0 0)]

abbrev col8Spec (n : Nat) : Int := Int.ofNat (spec8 n)

def col8Longs : List (Nat × Shape) :=
  [(0, .affine 65536 4 0),
    (65536, .affine 524288 58 0),
    (590066, .affine 3604238 0 0)]

end Airbender.Keccak.Split.ThetaRho.SetupProofs
