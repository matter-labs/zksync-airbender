module
public import Slop.WitnessCheck
public import Human.Circuits.MulDiv.Artifact
public import Slop.CleanCore.Circuit.Operations

@[expose] public section

/-! MUL/DIV witness tests by evaluation (`Slop/WitnessCheck.lean`): the checked tables of the imported lookups. -/

namespace Airbender.MulDiv
open Verification
variable {p : Nat} [Fact p.Prime]

/-- A `pairTable` (key `n < length`, value `value n`), checked by its definition. -/
def pairChecked (name : String) (length : Nat) (value : Nat → Nat) : CheckedTable (ZMod p) where
  table := (pairTable name length value).toRaw
  check
    | [x, y] => decide (x.val < length) && decide (y = ((value x.val : Nat) : ZMod p))
    | _ => false
  sound row h := by
    obtain ⟨⟨xs⟩, size⟩ := row
    have two : xs.length = 2 := size
    match xs, two with
    | [x, y], _ =>
      have both := Bool.and_eq_true_iff.mp h
      exact (pairTable (p := p) name length value).implied_by_completeness #[] (x, y)
        ⟨⟨x.val, of_decide_eq_true both.1⟩, Prod.ext (ZMod.natCast_zmod_val x).symm (of_decide_eq_true both.2)⟩
    | [], two | [_], two | _ :: _ :: _ :: _, two => simp at two

/-- `range13Table`, checked. -/
def range13Checked : CheckedTable (ZMod p) := rangeChecked "Airbender.Range13" 8192

/-- The tables the imported lookups query, in order (eight 16-bit ranges, a register-is-zero query, low-byte
    queries, three 13-bit ranges), then the eight timestamp queries. -/
def checkedTables : List (CheckedTable (ZMod p)) :=
  List.replicate 8 range16Checked ++ [pairChecked "Airbender.RegIsZero" 131072 (fun n => if n = 0 then 1 else 0)] ++
    List.replicate 2 (pairChecked "Airbender.U16GetLowByte" 65536 (fun n => n % 256)) ++
    List.replicate 3 range13Checked ++
    List.replicate 2 (pairChecked "Airbender.U16GetLowByte" 65536 (fun n => n % 256)) ++
    List.replicate 8 timestampChecked

theorem holds_of_check {w : Nat → ZMod p} (check : checkOps w clockConstraints checkedTables = true) :
    FlatOperation.ConstraintsHoldFlat (environment w) clockConstraints :=
  holds_of_checkOps rfl check

end Airbender.MulDiv
