import Airbender.Proofs.Tables.BlockSlices
import Lean.Elab.Term

namespace Airbender.Setup.Proofs
open Lean Elab Command
set_option warningAsError true

private def literalNat (value : Lean.Expr) : CommandElabM Nat := do
  let reduced ← liftTermElabM (Lean.Meta.whnf value)
  let some result := reduced.rawNatLit? | throwError "imported extent did not reduce to a literal"
  return result

private partial def arrayExtent (value : Lean.Expr) : CommandElabM Nat := do
  let value := value.consumeMData
  if let .letE _ _ rhs body _ := value then return ← arrayExtent (body.instantiate1 rhs)
  if value.isConst then
    return ← arrayExtent (← getConstInfoDefn value.constName!).value
  let args := value.getAppArgs
  if value.getAppFn.isConstOf ``Array.append && args.size == 3 then
    return (← arrayExtent args[1]!) + (← arrayExtent args[2]!)
  if value.getAppFn.isConstOf ``Array.ofFn && args.size == 3 then
    return ← literalNat args[1]!
  if value.getAppFn.isConstOf ``Array.replicate && args.size == 3 then
    return ← literalNat args[1]!
  if value.getAppFn.isConstOf ``Array.range && args.size == 1 then
    return ← literalNat args[0]!
  return (← literalArray value).size

private def blockExtent (value : Lean.Expr) : CommandElabM Nat := do
  let value := value.consumeMData
  let args := value.getAppArgs
  if value.getAppFn.isConstOf ``Airbender.Setup.Block.affine && args.size == 3 then
    return ← literalNat args[0]!
  if value.getAppFn.isConstOf ``Airbender.Setup.Block.dense && args.size == 1 then
    return ← arrayExtent args[0]!
  if value.getAppFn.isConstOf ``Airbender.Setup.Block.periodic && args.size == 3 then
    let repeats ← literalNat args[0]!
    return repeats * (← arrayExtent args[2]!)
  throwError "unsupported imported block expression"

private def subtree (value : Lean.Expr) (right : Bool) : CommandElabM Lean.Expr := do
  let args := value.getAppArgs
  if value.getAppFn.isConstOf ``Array.append && args.size == 3 then
    return args[if right then 2 else 1]!
  let blocks ← literalArray value
  unless 2 ≤ blocks.size do
    throwError "imported literal block leaf cannot be partitioned further"
  let middle := blocks.size / 2
  return balancedArray (if right then blocks.extract middle blocks.size else blocks.extract 0 middle)

private def addData (name : Name) (type value : Lean.Expr) : CommandElabM Unit := do
  let height := getMaxHeight (← getEnv) value + 1
  liftCoreM <| addDecl (.defnDecl {
    name := name, levelParams := [], type, value, hints := .regular height, safety := .safe })
  modifyEnv (addNoncomputable · name)

/-- Copy exact imported subtrees or contiguous literal block elements. Extents only name proof
    indices; subsequent kernel certificates check the extents and reconstruction. -/
elab "literal_column_parts " name:ident " from " source:term " depth " depth:num : command => do
  let d := depth.getNat
  unless d ≤ 8 do throwError "imported column partition is too deep"
  let value ← liftTermElabM do
    let expression ← Lean.Elab.Term.elabTerm source (some (mkConst ``Airbender.Setup.Column))
    Lean.Meta.whnf expression
  let value := value.consumeMData
  unless value.getAppFn.isConstOf ``Airbender.Setup.Column.mk && value.getAppArgs.size == 1 do
    throwError "column projection did not reduce to an imported literal Column"
  let fullName := (← getCurrNamespace) ++ name.getId
  addData fullName (mkConst ``Airbender.Setup.Column) value
  let mut start := 0
  for part in [:2 ^ d] do
    let mut selected := value.getAppArgs[0]!
    for level in [:d] do
      selected ← subtree selected (part / 2 ^ (d - 1 - level) % 2 == 1)
    let blocks ← literalArray selected
    let lengths ← blocks.mapM blockExtent
    let extent := lengths.foldl (· + ·) 0
    addData (fullName.appendAfter s!"Blocks{part}")
      (mkApp (mkConst ``Array [Level.zero]) (mkConst ``Airbender.Setup.Block)) selected
    addData (fullName.appendAfter s!"Start{part}") (mkConst ``Nat) (mkNatLit start)
    addData (fullName.appendAfter s!"Size{part}") (mkConst ``Nat) (mkNatLit extent)
    start := start + extent

end Airbender.Setup.Proofs
