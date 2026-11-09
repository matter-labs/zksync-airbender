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

def constraints : List (FlatOperation F) → List (Expression F)
  | [] => []
  | assert e :: ops => e :: constraints ops
  | lookup _ :: ops => constraints ops

def lookups : List (FlatOperation F) → List (Lookup F)
  | [] => []
  | lookup l :: ops => l :: lookups ops
  | assert _ :: ops => lookups ops

/-- Induction principle for `FlatOperation` lists. -/
def induct {motive : List (FlatOperation F) → Sort _}
    (empty : motive [])
    (assert : ∀ e ops, motive ops → motive (.assert e :: ops))
    (lookup : ∀ l ops, motive ops → motive (.lookup l :: ops))
    (ops : List (FlatOperation F)) : motive ops :=
  match ops with
  | [] => empty
  | .assert e :: ops => assert e ops (induct empty assert lookup ops)
  | .lookup l :: ops => lookup l ops (induct empty assert lookup ops)

theorem constraintsHoldFlat_iff_forall_mem [Field F] {eval : Environment F} {ops : List (FlatOperation F)} :
    ConstraintsHoldFlat eval ops ↔
      (∀ e ∈ constraints ops, eval e = 0) ∧ (∀ l ∈ lookups ops, l.Contains eval) := by
  induction ops using FlatOperation.induct <;>
    simp_all [ConstraintsHoldFlat, constraints, lookups, and_assoc]
  tauto

end FlatOperation

end Airbender
