module
public import Mathlib.Tactic.NormNum
-- Clean's Mathlib/Lean imports for this file, re-exported so importers see what they saw through Clean
public import Lean.Meta.Tactic.Simp.RegisterCommand
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Analysis.Normed.Ring.Lemmas

/-! # Splitting a 16-bit value into two bytes (Clean `Clean.Utils.Field`, pinned b41c196). -/

@[expose] public section

namespace Airbender

namespace ByteUtils
def splitTwoBytes (i : Fin (256 * 256)) : Fin 256 × Fin 256 :=
  let x := i.val / 256
  let y := i.val % 256
  have x_lt : x < 256 := by simp [x, Nat.div_lt_iff_lt_mul]
  have y_lt : y < 256 := Nat.mod_lt i.val (by norm_num)
  (⟨ x, x_lt ⟩, ⟨ y, y_lt ⟩)

end ByteUtils

end Airbender
