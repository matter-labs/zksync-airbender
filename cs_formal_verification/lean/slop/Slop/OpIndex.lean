import Clean.Circuit.Operations
import Slop.OpIndexAttr

/-! Per-index interface lemmas for an imported circuit (`import_clean`): one lemma per constraint and
per lookup, `(FlatOperation.constraints (C args)).get ⟨k, h⟩ = e_k`, proven once by `rfl`. Proofs cite them
instead of unfolding the whole operation list at every use (lean-strategies §2.1).

`derive_op_index C` adds `C.constraint_k` and `C.lookup_k` to the `op_index` simp set; the tactic
`op_index at h ⊢` normalizes literal indices and rewrites with them. -/

open Lean Meta Elab Command

namespace Airbender.OpIndex

private def opArg? (e : Expr) (op : Name) : Option Expr :=
  if e.isAppOfArity op 2 then some e.appArg! else none

/-- The elements of an elaborated list literal: long literals elaborate to `have` chunks joined by `++`. -/
private partial def listElems (e : Expr) : MetaM (Array Expr) := do
  let e := e.consumeMData
  if e.isAppOfArity ``List.cons 3 then
    return #[e.appFn!.appArg!] ++ (← listElems e.appArg!)
  else if e.isAppOfArity ``List.nil 1 then
    return #[]
  else if e.isAppOfArity ``HAppend.hAppend 6 || e.isAppOfArity ``List.append 3 then
    return (← listElems e.appFn!.appArg!) ++ (← listElems e.appArg!)
  else
    throwError "not a list literal: {e.getAppFn}"

/-- Fallback for lists defined by list operations (`drop`, `take`, `++` of imported lists): evaluate to cons cells. -/
private partial def evalElems (e : Expr) : MetaM (Array Expr) := do
  let e ← whnf e
  if e.isAppOfArity ``List.cons 3 then
    return #[e.appFn!.appArg!] ++ (← evalElems e.appArg!)
  else if e.isAppOfArity ``List.nil 1 then
    return #[]
  else
    throwError "cannot evaluate the operation list: {e.getAppFn}"

/-- `∀ args (h : k < (sel (C args)).length), (sel (C args)).get ⟨k, h⟩ = rhs`, by `rfl`. -/
private def addIndexLemma (declName : Name) (levelNames : List Name) (xs : Array Expr) (constAt : Expr)
    (selector : Name) (k : Nat) (rhs : Expr) : MetaM Unit := do
  let list ← mkAppM selector #[constAt]
  let bound ← mkAppM ``LT.lt #[mkNatLit k, ← mkAppM ``List.length #[list]]
  withLocalDeclD `h bound fun h => do
    let get ← mkAppM ``List.get #[list, ← mkAppM ``Fin.mk #[mkNatLit k, h]]
    let type ← mkForallFVars (xs.push h) (← mkEq get rhs)
    let value ← mkLambdaFVars (xs.push h) (← mkEqRefl get)
    addDecl <| .thmDecl { name := declName, levelParams := levelNames, type, value }
    let some ext ← getSimpExtension? `op_index | throwError "missing simp attribute op_index"
    addSimpTheorem ext declName (post := true) (inv := false) .global (eval_prio default)

elab "derive_op_index " id:ident : command => do
  let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let info ← getConstInfoDefn name
  let levels := info.levelParams.map mkLevelParam
  let (constraints, lookups) ← liftTermElabM <| lambdaTelescope info.value fun xs body => do
    let constAt := mkAppN (mkConst name levels) xs
    let elems ← try listElems (← zetaReduce body) catch _ => evalElems constAt
    let mut c := 0
    let mut l := 0
    for op in elems do
      if let some e := opArg? op ``FlatOperation.assert then
        addIndexLemma (name ++ Name.mkSimple s!"constraint_{c}") info.levelParams xs constAt ``FlatOperation.constraints c e
        c := c + 1
      else if let some e := opArg? op ``FlatOperation.lookup then
        addIndexLemma (name ++ Name.mkSimple s!"lookup_{l}") info.levelParams xs constAt ``FlatOperation.lookups l e
        l := l + 1
    return (c, l)
  logInfo m!"{name}: {constraints} constraint and {lookups} lookup lemmas"

end Airbender.OpIndex

/-- Rewrite literal-index accesses `(constraints C).get ⟨k, _⟩` / `(lookups C).get ⟨k, _⟩` with the generated lemmas. -/
macro "op_index" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp only [op_index, Fin.isValue, Fin.val_zero, Fin.val_mk, Fin.val_ofNat, Nat.reduceMul, Nat.reduceAdd,
    Nat.reduceMod] $[$loc]?)
