module
public import Human.Circuits.JumpBranchSlt.Jump
public import Human.Helpers.Core.BabyBearPrime
public import Slop.AddSub.Selectors
public import Slop.JumpBranchSlt.Branch
public import Slop.JumpBranchSlt.Jump
public import Slop.MulDiv.Product
public import Human.Circuits.MulDiv.Operation
public import Slop.MulDiv.Values
public import Slop.SubwordMemory.Values
public import Slop.Trace.CompositionCore
public import Slop.Trace.RowContext
public import Slop.Eval
public import Mathlib.Tactic.IntervalCases
public import Slop.ShiftBinop.Arithmetic

@[expose] public section

namespace Tests.Shifts
open Airbender

-- Three shifts and REV8, amounts 0/31, immediate/register preprocessing, a negative
-- source and PC carry. Register amounts 32/63 exercise low-five-bit truncation.
def amount (tag : Fin 4) (zero : Bool) : Nat := if tag.val = 3 ∨ zero then 0 else 31
def code (tag : Fin 4) : Nat := if tag.val = 3 then 5 else tag.val + 1
def zeroRight (tag : Fin 4) (immediate : Bool) : Bool := immediate || tag.val = 3
def source : BitVec 32 := 2158742802
def sourceByte (i : Nat) : Nat := (source.extractLsb' (8 * i) 8).toNat
-- Concrete expected bytes; soundness checks this value against original Sail.
def result (tag : Fin 4) (zero : Bool) : Nat :=
  if tag.val = 3 then 315468672 else
    (Verification.shiftOperation (code tag) source (amount tag zero)).toNat
def part (tag : Fin 4) (zero : Bool) (i j : Nat) : Nat :=
  (BitVec.extractLsb' (8 * j) 8
    (Verification.shiftByteContribution i (sourceByte i) (amount tag zero) (code tag))).toNat

def row (tag : Fin 4) (immediate zero : Bool) : Nat → ZMod babyBearModulus
  | 0 => 65532
  | 4 | 5 | 7 | 11 | 14 => 1
  | 6 => if zeroRight tag immediate then 0 else 2
  | 8 => if immediate then amount tag zero else 0
  | 10 => code tag
  | 15 => 4
  | 19 => sourceByte 0 | 20 => sourceByte 1
  | 21 => sourceByte 2 | 22 => sourceByte 3
  | 25 | 52 => if zeroRight tag immediate then 0 else amount tag zero + 32
  | 27 => if zeroRight tag immediate then 0 else 52
  | 28 => if zeroRight tag immediate then 0 else 18
  | 31 => (result tag zero % 65536 : Nat)
  | 32 => (result tag zero / 65536 : Nat)
  | 35 | 54 => if zeroRight tag immediate then 0 else amount tag zero
  | 55 => 8
  | n => if 36 ≤ n ∧ n < 52 then part tag zero ((n - 36) / 4) ((n - 36) % 4) else
    if 56 ≤ n ∧ n < 92 then
      let i := (n - 56) / 9
      match (n - 56) % 9 with
      | 0 => i | 1 => sourceByte i | 2 => amount tag zero | 3 => code tag
      | 8 => 9 | j => part tag zero i (j - 4)
    else 0

example : ¬ (Verification.shiftBinopLookup
    (#v[.const 0, .const 18, .const 32, .const 1, .const 0, .const 0,
      .const 0, .const 0, .const 0, .const 9] :
        Vector (Expression (ZMod babyBearModulus)) 10)).Contains
          (Verification.environment (fun _ => 0)) := by
  intro h
  have bound := (Verification.shift_lookup (by decide) h (by rfl)).2.2.1
  change (32 : ZMod babyBearModulus).val < 32 at bound
  exact (by decide : ¬ (32 : ZMod babyBearModulus).val < 32) bound

end Tests.Shifts
