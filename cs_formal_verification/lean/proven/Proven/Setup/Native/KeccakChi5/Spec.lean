module
public import Proven.KeccakSplit.Setup.Facts
public import Human.Circuits.KeccakSplit.Chi5.SetupArtifact
public import Proven.Setup.Scan

@[expose] public section

/- Column formulas of the native chi setup of the split Keccak workers, in the form that the kernel evaluates fast,
   and their agreement with the row formulas `spec0` to `spec10`. The controller rows keep the row formula, and the
   kernel checks them one by one. -/

namespace Airbender.Keccak.Split.Chi5.SetupProofs
open Airbender.Import.Setup.Scan Airbender.Keccak.Split.SetupProofs

/-- The value of a row in each region: the chi table (`chi`), the controller rows (`controller`), then zero
    padding. -/
def byRegion (n : Nat) (chi controller : Nat) : Nat :=
  pick (Nat.blt n 1048576) chi <| pick (Nat.blt n 1048697) controller 0

/-- Chi of three four-bit slices: `a ^ (!b & c)`. -/
def chiNibble (a b c : Nat) : Nat := Nat.xor a (Nat.land (Nat.xor 15 b) c)

def column0 (n : Nat) : Nat := byRegion n (Nat.mod n 16) (spec0 n)
def column1 (n : Nat) : Nat := byRegion n (Nat.mod (Nat.div n 16) 16) (spec1 n)
def column2 (n : Nat) : Nat := byRegion n (Nat.mod (Nat.div n 256) 16) (spec2 n)
def column3 (n : Nat) : Nat := byRegion n (Nat.mod (Nat.div n 4096) 16) (spec3 n)
def column4 (n : Nat) : Nat := byRegion n (Nat.mod (Nat.div n 65536) 16) (spec4 n)
def column5 (n : Nat) : Nat :=
  byRegion n (chiNibble (Nat.mod n 16) (Nat.mod (Nat.div n 16) 16) (Nat.mod (Nat.div n 256) 16)) (spec5 n)
def column6 (n : Nat) : Nat :=
  byRegion n (chiNibble (Nat.mod (Nat.div n 16) 16) (Nat.mod (Nat.div n 256) 16) (Nat.mod (Nat.div n 4096) 16))
    (spec6 n)
def column7 (n : Nat) : Nat :=
  byRegion n
    (chiNibble (Nat.mod (Nat.div n 256) 16) (Nat.mod (Nat.div n 4096) 16) (Nat.mod (Nat.div n 65536) 16))
    (spec7 n)
def column8 (n : Nat) : Nat :=
  byRegion n (chiNibble (Nat.mod (Nat.div n 4096) 16) (Nat.mod (Nat.div n 65536) 16) (Nat.mod n 16)) (spec8 n)
def column9 (n : Nat) : Nat :=
  byRegion n (chiNibble (Nat.mod (Nat.div n 65536) 16) (Nat.mod n 16) (Nat.mod (Nat.div n 16) 16)) (spec9 n)
def column10 (n : Nat) : Nat := byRegion n 65 (spec10 n)

theorem columns_eq (n : Nat) :
    column0 n = spec0 n ∧ column1 n = spec1 n ∧ column2 n = spec2 n ∧ column3 n = spec3 n ∧
    column4 n = spec4 n ∧ column5 n = spec5 n ∧ column6 n = spec6 n ∧ column7 n = spec7 n ∧
    column8 n = spec8 n ∧ column9 n = spec9 n ∧ column10 n = spec10 n := by
  simp only [column0, column1, column2, column3, column4, column5, column6, column7, column8, column9, column10,
    byRegion, chiNibble, spec0, spec1, spec2, spec3, spec4, spec5, spec6, spec7, spec8, spec9, spec10, chiOut, nib,
    nat_blt, pick_decide, nat_div, nat_mod, nat_xor, nat_land, Nat.reducePow, Nat.reduceAdd, Nat.reduceMod,
    Nat.pow_zero, Nat.div_one]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> split_ifs <;> rfl

end Airbender.Keccak.Split.Chi5.SetupProofs
