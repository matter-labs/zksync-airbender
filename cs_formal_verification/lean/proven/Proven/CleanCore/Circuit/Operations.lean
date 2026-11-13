module
public import CleanCore.Circuit.Operations

/-! # The constraint and lookup lists of a flat circuit, and the lemma the proofs cite (Clean
`Clean.Circuit.Operations`, pinned b41c196, transcribed with proofs). -/

@[expose] public section

namespace Airbender

variable {F : Type}

namespace FlatOperation

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
