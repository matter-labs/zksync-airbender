module
public import Proven.KeccakSplit.Setup.Chi5.Spec

@[expose] public section

/- Long blocks of each imported column, matched by shape: the import's grid blocks and the
   affine runs longer than 200 rows (the other blocks are checked row by row in `Rows`). -/

namespace Airbender.Keccak.Split.Chi5.SetupProofs

open Airbender.Import.Setup Airbender.Import.Setup.Proofs

set_option warningAsError true

abbrev col0Spec (n : Nat) : Int := Int.ofNat (spec0 n)

def col0Longs : List (Nat × Shape) :=
  [(0, .grid 1048576 (.digit 1 16)),
    (1048697, .affine 3145607 0 0)]

abbrev col1Spec (n : Nat) : Int := Int.ofNat (spec1 n)

def col1Longs : List (Nat × Shape) :=
  [(0, .grid 1048576 (.digit 16 16)),
    (1048697, .affine 3145607 0 0)]

abbrev col2Spec (n : Nat) : Int := Int.ofNat (spec2 n)

def col2Longs : List (Nat × Shape) :=
  [(0, .grid 1048576 (.digit 256 16)),
    (1048697, .affine 3145607 0 0)]

abbrev col3Spec (n : Nat) : Int := Int.ofNat (spec3 n)

def col3Longs : List (Nat × Shape) :=
  [(0, .grid 1048576 (.digit 4096 16)),
    (1048697, .affine 3145607 0 0)]

abbrev col4Spec (n : Nat) : Int := Int.ofNat (spec4 n)

def col4Longs : List (Nat × Shape) :=
  [(0, .grid 1048576 (.digit 65536 16)),
    (1048697, .affine 3145607 0 0)]

abbrev col5Spec (n : Nat) : Int := Int.ofNat (spec5 n)

def col5Longs : List (Nat × Shape) :=
  [(0, .grid 1048576 (.chi 0)),
    (1048697, .affine 3145607 0 0)]

abbrev col6Spec (n : Nat) : Int := Int.ofNat (spec6 n)

def col6Longs : List (Nat × Shape) :=
  [(0, .grid 1048576 (.chi 1)),
    (1048697, .affine 3145607 0 0)]

abbrev col7Spec (n : Nat) : Int := Int.ofNat (spec7 n)

def col7Longs : List (Nat × Shape) :=
  [(0, .grid 1048576 (.chi 2)),
    (1048697, .affine 3145607 0 0)]

abbrev col8Spec (n : Nat) : Int := Int.ofNat (spec8 n)

def col8Longs : List (Nat × Shape) :=
  [(0, .grid 1048576 (.chi 3)),
    (1048697, .affine 3145607 0 0)]

abbrev col9Spec (n : Nat) : Int := Int.ofNat (spec9 n)

def col9Longs : List (Nat × Shape) :=
  [(0, .grid 1048576 (.chi 4)),
    (1048697, .affine 3145607 0 0)]

abbrev col10Spec (n : Nat) : Int := Int.ofNat (spec10 n)

def col10Longs : List (Nat × Shape) :=
  [(0, .affine 1048576 65 0),
    (1048697, .affine 3145607 0 0)]

end Airbender.Keccak.Split.Chi5.SetupProofs
