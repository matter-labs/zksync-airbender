module
public import Proven.KeccakSplit.Setup.Facts
public import Human.Circuits.KeccakSplit.ThetaRho.SetupArtifact
public import Proven.Setup.Scan

@[expose] public section

/- Column formulas of the native theta/rho setup of the split Keccak workers, in the form that the kernel evaluates
   fast, and their agreement with the row formulas `spec0` to `spec8`. The controller rows keep the row formula, and
   the kernel checks them one by one. -/

namespace Airbender.Keccak.Split.ThetaRho.SetupProofs
open Airbender.Import.Setup.Scan Airbender.Keccak.Split.SetupProofs

/-- The value of a row in each region: the byte XOR table, the XOR-and-split table of `n - 65536`, the controller
    rows (`controller`), then zero padding. -/
def byRegion (n : Nat) (xor split : Nat → Nat) (controller : Nat) : Nat :=
  pick (Nat.blt n 65536) (xor n) <|
  pick (Nat.blt n 589824) (split (Nat.sub n 65536)) <|
  pick (Nat.blt n 590066) controller 0

def column0 (n : Nat) : Nat := byRegion n (fun i => Nat.div i 256) (fun m => Nat.mod m 256) (spec0 n)
def column1 (n : Nat) : Nat :=
  byRegion n (fun i => Nat.mod i 256) (fun m => Nat.mod (Nat.div m 256) 256) (spec1 n)
def column2 (n : Nat) : Nat :=
  byRegion n (fun i => Nat.xor (Nat.div i 256) (Nat.mod i 256)) (fun m => Nat.div m 65536) (spec2 n)
def column3 (n : Nat) : Nat :=
  byRegion n (fun _ => 0)
    (fun m => Nat.mod (Nat.mul (Nat.xor (Nat.mod m 256) (Nat.mod (Nat.div m 256) 256)) (Nat.pow 2 (Nat.div m 65536)))
      256) (spec3 n)
def column4 (n : Nat) : Nat :=
  byRegion n (fun _ => 0)
    (fun m => Nat.div (Nat.xor (Nat.mod m 256) (Nat.mod (Nat.div m 256) 256)) (Nat.pow 2 (Nat.sub 8 (Nat.div m 65536))))
    (spec4 n)
def column5 (n : Nat) : Nat := byRegion n (fun _ => 0) (fun _ => 0) (spec5 n)
def column6 (n : Nat) : Nat := byRegion n (fun _ => 0) (fun _ => 0) (spec6 n)
def column7 (n : Nat) : Nat := byRegion n (fun _ => 0) (fun _ => 0) (spec7 n)
def column8 (n : Nat) : Nat := byRegion n (fun _ => 4) (fun _ => 58) (spec8 n)

theorem columns_eq (n : Nat) :
    column0 n = spec0 n ∧ column1 n = spec1 n ∧ column2 n = spec2 n ∧ column3 n = spec3 n ∧
    column4 n = spec4 n ∧ column5 n = spec5 n ∧ column6 n = spec6 n ∧ column7 n = spec7 n ∧
    column8 n = spec8 n := by
  simp only [column0, column1, column2, column3, column4, column5, column6, column7, column8, byRegion, spec0, spec1,
    spec2, spec3, spec4, spec5, spec6, spec7, spec8, splitKeyA, splitKeyB, splitShift, nat_blt, pick_decide, nat_sub, nat_div,
    nat_mod, nat_mul, nat_pow, nat_xor]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> split_ifs <;> first | rfl | omega

end Airbender.Keccak.Split.ThetaRho.SetupProofs
