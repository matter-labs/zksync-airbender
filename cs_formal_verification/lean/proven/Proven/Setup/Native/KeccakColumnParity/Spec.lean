module
public import Proven.KeccakSplit.Setup.ColumnParity.Spec
public import Human.Circuits.KeccakSplit.ColumnParity.SetupArtifact
public import Proven.Setup.Scan

@[expose] public section

/- Column formulas of the native column-parity setup of the split Keccak workers, in the form that the kernel
   evaluates fast, and their agreement with the row formulas `spec0` to `spec7`. The controller rows keep the row
   formula, and the kernel checks them one by one. -/

namespace Airbender.Keccak.Split.ColumnParity.SetupProofs
open Airbender.Import.Setup.Scan Airbender.Keccak.Split.SetupProofs

/-- The value of a row in each region: the iota table, the controller rows (`controller`), the five-input XOR table
    of `n - 65780`, then zero padding. -/
def byRegion (n : Nat) (iota : Nat → Nat) (controller : Nat) (parity : Nat → Nat) : Nat :=
  pick (Nat.blt n 65536) (iota n) <|
  pick (Nat.blt n 65780) controller <|
  pick (Nat.blt n 1114356) (parity (Nat.sub n 65780)) 0

def column0 (n : Nat) : Nat := byRegion n (fun i => Nat.mod i 256) (spec0 n) (fun m => Nat.mod m 16)
def column1 (n : Nat) : Nat :=
  byRegion n (fun i => Nat.div i 256) (spec1 n) (fun m => Nat.mod (Nat.div m 16) 16)
def column2 (n : Nat) : Nat :=
  byRegion n (fun i => Nat.xor (Nat.mod i 256) (rcByte (Nat.div i 256))) (spec2 n)
    (fun m => Nat.mod (Nat.div m 256) 16)
def column3 (n : Nat) : Nat := byRegion n (fun _ => 0) (spec3 n) (fun m => Nat.mod (Nat.div m 4096) 16)
def column4 (n : Nat) : Nat := byRegion n (fun _ => 0) (spec4 n) (fun m => Nat.mod (Nat.div m 65536) 16)
def column5 (n : Nat) : Nat :=
  byRegion n (fun _ => 0) (spec5 n) fun m =>
    Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.mod m 16) (Nat.mod (Nat.div m 16) 16)) (Nat.mod (Nat.div m 256) 16))
      (Nat.mod (Nat.div m 4096) 16)) (Nat.mod (Nat.div m 65536) 16)
def column6 (n : Nat) : Nat := byRegion n (fun _ => 0) (spec6 n) (fun _ => 0)
def column7 (n : Nat) : Nat := byRegion n (fun _ => 38) (spec7 n) (fun _ => 64)

set_option maxRecDepth 100000 in
theorem columns_eq (n : Nat) :
    column0 n = spec0 n ∧ column1 n = spec1 n ∧ column2 n = spec2 n ∧ column3 n = spec3 n ∧
    column4 n = spec4 n ∧ column5 n = spec5 n ∧ column6 n = spec6 n ∧ column7 n = spec7 n := by
  simp only [column0, column1, column2, column3, column4, column5, column6, column7, byRegion, spec0, spec1, spec2,
    spec3, spec4, spec5, spec6, spec7, nib, nat_blt, pick_decide, nat_sub, nat_div, nat_mod, nat_xor, Nat.reducePow,
    Nat.pow_zero, Nat.div_one]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> split_ifs <;> omega

end Airbender.Keccak.Split.ColumnParity.SetupProofs
