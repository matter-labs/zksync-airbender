module
public import CleanCore.Circuit.Lookup
public import Mathlib.Tactic.Tauto

/-! # Flat circuit operations (Clean `Clean.Circuit.Operations`, pinned b41c196)

An imported circuit is a list of operations: assertions (`e = 0`) and lookups. `ConstraintsHoldFlat env ops`
says every operation holds in `env`. Same definitions as Clean. Deviation: Clean's `FlatOperation` also has
`witness` (witness generation, no constraint) and `interact` (channel interaction, checked globally, no
local constraint); our circuits emit neither, and both are no-ops in Clean's `ConstraintsHoldFlat`.
`CleanEquivalence.constraintsHoldFlat_iff` states the correspondence. -/

@[expose] public section

namespace Airbender

variable {F : Type}

inductive FlatOperation (F : Type) where
  | assert : Expression F → FlatOperation F
  | lookup : Lookup F → FlatOperation F

namespace FlatOperation

def ConstraintsHoldFlat [Field F] (eval : Environment F) : List (FlatOperation F) → Prop
  | [] => True
  | op :: ops => match op with
    | assert e => (eval e = 0) ∧ ConstraintsHoldFlat eval ops
    | lookup l => l.Contains eval ∧ ConstraintsHoldFlat eval ops

end FlatOperation

end Airbender
