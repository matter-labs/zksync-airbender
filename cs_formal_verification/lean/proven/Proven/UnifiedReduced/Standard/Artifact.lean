module
public import Proven.UnifiedReduced.Standard.Profile
public import Proven.UnifiedReduced.OpIndex
public import Proven.UnifiedReduced.Proth120.Standard.Artifact
public meta import Lean

@[expose] public section
namespace Airbender.UnifiedReduced.Standard
open Lean Meta Elab Term

/-- Read a fully elaborated, kernel-checked operation list. -/
private meta def elements (list : Lean.Expr) : MetaM (Array Lean.Expr) := do
  let mut current := list
  let mut result := #[]
  for _ in [:(120 + 18)] do
    let next ← whnf current
    unless next.isAppOfArity ``List.cons 3 do throwError "unified row has fewer than 138 operations"
    result := result.push (← whnf next.appFn!.appArg!)
    current := next.appArg!
  unless (← whnf current).isAppOfArity ``List.nil 1 do throwError "unified row has more than 138 operations"
  return result

private meta def coefficients (replacements : Array (Lean.Expr × Lean.Expr)) : Lean.Expr → MetaM Lean.Expr
  | e@(.app (.app fn x) y) => do
    if e.isAppOfArity ``Airbender.Expression.const 2 then
      for (old, new) in replacements do
        if ← isDefEq y old then return mkApp2 fn x new
    if e.isAppOfArity ``Airbender.Expression.add 3 || e.isAppOfArity ``Airbender.Expression.mul 3 then
      return mkApp2 fn (← coefficients replacements x) (← coefficients replacements y)
    return e
  | e => return e

/-- Reuse the shared equations and lookups verbatim. Only the two modular polynomials
    switch shape. ROM size and inverse coefficients are parameters of the remaining equations. -/
elab "standard_row " profile:ident setup:ident : term => do
  let bb ← elabTerm (← `(Airbender.UnifiedReduced.importedConstraints $setup)) none
  let wrap ← elabTerm (← `(Airbender.UnifiedReduced.Proth120.Standard.importedConstraints $setup)) none
  let left ← elements bb
  let right ← elements wrap
  let field := (← inferType left[0]!).appArg!
  let scalar (t : TSyntax `term) := elabTerm t field
  let rom ← scalar (← `(Int.cast (-(Profile.romLimbs $profile : Int))))
  let inv ← scalar (← `(Profile.byteInv $profile))
  let time ← scalar (← `(Int.cast (Int.ofNat (Airbender.CircuitField.negInvPow (Profile.modulus $profile) 19))))
  let square ← scalar (← `(Profile.clockSquare $profile))
  let param ← elabTerm profile none
  let replacements := #[rom, inv, time, square].map fun e => (e.replaceFVar param (mkConst ``Profile.babyBear), e)
  let mut ops := #[]
  for i in [:left.size] do
    let op := left[i]!
    if i == 1 || i == 2 then
      let e ← mkAppM ``Profile.choose #[param, op.appArg!, right[i]!.appArg!]
      ops := ops.push (mkApp op.appFn! e)
    else if [36, 47, 59, 60, 77, 78, 89, 90].contains i then
      ops := ops.push (mkApp op.appFn! (← coefficients replacements op.appArg!))
    else ops := ops.push op
  mkListLit (← inferType left[0]!) ops.toList

set_option maxRecDepth 16384

def importedConstraints {p : Nat} [Fact p.Prime] (profile : Profile) (setup : Table (ZMod p) (fields 10)) :
    List (FlatOperation (ZMod p)) := standard_row profile setup

set_option maxHeartbeats 4000000 in
theorem babyBear_operations {p : Nat} [Fact p.Prime] (setup : Table (ZMod p) (fields 10)) :
    importedConstraints .babyBear setup = UnifiedReduced.importedConstraints setup := by rfl

set_option maxHeartbeats 4000000 in
theorem proth120_operations {p : Nat} [Fact p.Prime] (setup : Table (ZMod p) (fields 10)) :
    importedConstraints .proth120 setup = Proth120.Standard.importedConstraints setup := by rfl

theorem proth120_holds {p : Nat} [Fact p.Prime] {setup : Table (ZMod p) (fields 10)} {env : Environment (ZMod p)}
    (h : FlatOperation.ConstraintsHoldFlat env (Proth120.importedConstraints setup)) :
    FlatOperation.ConstraintsHoldFlat env (importedConstraints .proth120 setup) := by
  rw [proth120_operations]
  exact Proth120.Standard.holds h

theorem constraint_count {p : Nat} [Fact p.Prime] (profile : Profile) (setup : Table (ZMod p) (fields 10)) :
    (FlatOperation.constraints (importedConstraints profile setup)).length = 120 := rfl

theorem lookup_count {p : Nat} [Fact p.Prime] (profile : Profile) (setup : Table (ZMod p) (fields 10)) :
    (FlatOperation.lookups (importedConstraints profile setup)).length = 18 := rfl

/-- All eight timestamp queries and the logical columns used by the row state, three memory
    ports, and decoder agree across the artifacts. -/
theorem timestamps {p : Nat} [Fact p.Prime] :
    UnifiedReduced.importedConstraintsTimestampLookups (p := p) = Proth120.importedConstraintsTimestampLookups := rfl

theorem columns : UnifiedReduced.importedConstraintsTraceColumns = Proth120.importedConstraintsTraceColumns ∧
    UnifiedReduced.importedConstraintsMemoryPorts = Proth120.importedConstraintsMemoryPorts ∧
    UnifiedReduced.importedConstraintsDecoderColumns = Proth120.importedConstraintsDecoderColumns := ⟨rfl, rfl, rfl⟩

set_option maxRecDepth 100000 in
derive_op_index Airbender.UnifiedReduced.Standard.importedConstraints

end Airbender.UnifiedReduced.Standard
