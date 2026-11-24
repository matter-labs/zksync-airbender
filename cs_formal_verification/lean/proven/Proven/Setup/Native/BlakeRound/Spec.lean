module
public import Proven.Blake2Round.Setup.Spec
public import Human.Circuits.Blake2Round.SetupArtifact
public import Proven.Setup.Scan

@[expose] public section

/- Column formulas of the native BLAKE2 round setup, in the form that the kernel evaluates fast, and their agreement
   with the row formulas `Blake2Round.SetupProofs.spec0` to `spec5`. -/

namespace Airbender.Blake2Round.SetupProofs
open Airbender.Import.Setup.Scan

/-- The value of a row in each region: the XOR tables with 8-, 7- and 9-bit keys, the XOR tables with carry with 8-
    and 7-bit keys, the split XOR table, then zero padding. -/
def byRegion (n : Nat) (xor8 xor7 xor9 carry8 carry7 split : Nat → Nat) : Nat :=
  pick (Nat.blt n 65536) (xor8 n) <|
  pick (Nat.blt n 81920) (xor7 (Nat.sub n 65536)) <|
  pick (Nat.blt n 344064) (xor9 (Nat.sub n 81920)) <|
  pick (Nat.blt n 540672) (carry8 (Nat.sub n 344064)) <|
  pick (Nat.blt n 589824) (carry7 (Nat.sub n 540672)) <|
  pick (Nat.blt n 606208) (split (Nat.sub n 589824)) 0

def column0 (n : Nat) : Nat :=
  byRegion n (fun i => Nat.div i 256) (fun i => Nat.div i 128) (fun i => Nat.div i 512)
    (fun i => Nat.div (Nat.mod i 65536) 256) (fun i => Nat.div (Nat.mod i 16384) 128) (fun i => Nat.div i 1024)
def column1 (n : Nat) : Nat :=
  byRegion n (fun i => Nat.mod i 256) (fun i => Nat.mod i 128) (fun i => Nat.mod i 512) (fun i => Nat.mod i 256)
    (fun i => Nat.mod i 128) (fun i => Nat.mod (Nat.div i 128) 8)
def column2 (n : Nat) : Nat :=
  byRegion n (fun i => Nat.xor (Nat.div i 256) (Nat.mod i 256)) (fun i => Nat.xor (Nat.div i 128) (Nat.mod i 128))
    (fun i => Nat.xor (Nat.div i 512) (Nat.mod i 512)) (fun i => Nat.div i 65536) (fun i => Nat.div i 16384)
    (fun i => Nat.mod (Nat.div i 8) 16)
def column3 (n : Nat) : Nat :=
  byRegion n (fun _ => 0) (fun _ => 0) (fun _ => 0)
    (fun i => Nat.xor (Nat.div (Nat.mod i 65536) 256) (Nat.mod i 256))
    (fun i => Nat.xor (Nat.div (Nat.mod i 16384) 128) (Nat.mod i 128)) (fun i => Nat.mod i 8)
def column4 (n : Nat) : Nat :=
  byRegion n (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0)
    (fun i => Nat.lor (Nat.xor (Nat.div i 1024) (Nat.mod (Nat.div i 8) 16))
      (Nat.shiftLeft (Nat.xor (Nat.mod (Nat.div i 128) 8) (Nat.mod i 8)) 4))
def column5 (n : Nat) : Nat :=
  byRegion n (fun _ => 4) (fun _ => 19) (fun _ => 20) (fun _ => 55) (fun _ => 56) (fun _ => 57)

theorem nat_shiftLeft (a b : Nat) : Nat.shiftLeft a b = a <<< b := rfl

theorem columns_eq (n : Nat) :
    column0 n = spec0 n ∧ column1 n = spec1 n ∧ column2 n = spec2 n ∧ column3 n = spec3 n ∧
    column4 n = spec4 n ∧ column5 n = spec5 n := by
  simp only [column0, column1, column2, column3, column4, column5, byRegion, spec0, spec1, spec2, spec3, spec4,
    spec5, nat_blt, pick_decide, nat_sub, nat_div, nat_mod, nat_xor, nat_lor, nat_shiftLeft]
  split_ifs <;> first | omega | simp

end Airbender.Blake2Round.SetupProofs
