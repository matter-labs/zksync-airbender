import Airbender.Proofs.FullUnsigned.SourceIndexPartitions
import Airbender.Import.SetupSourceBank

namespace Airbender.Setup.SourceBank
open Lean Meta Elab Command
set_option warningAsError true
set_option Elab.async false

private def branchProof (split left right : Lean.Expr) (proof : Lean.Expr)
    (onLeft : Bool) : MetaM Lean.Expr := do
  withLocalDeclD `child (mkConst ``Bank) fun child => do
    let body := if onLeft then mkApp3 (mkConst ``Bank.branch) split child right
      else mkApp3 (mkConst ``Bank.branch) split left child
    let context ← mkLambdaFVars #[child] body
    mkAppM ``congrArg #[context, proof]

/-- Rebuild only the selected path. Every other child stays as its original
expression. Congruence proves equality of the entire bank. -/
private partial def replaceArrayPath (original : Lean.Expr) (index : Nat)
    (entries partitionProof : Lean.Expr) : MetaM (Lean.Expr × Lean.Expr) := withTransparency .all do
  let bank ← whnf original
  if bank.isAppOf ``Bank.leaf then
    let description ← whnf bank.getAppArgs[0]!
    unless description.isAppOf ``Description.indexedArray do
      throwError "expected the original indexed source array"
    let children := description.getAppArgs[0]!
    let replacement := mkApp2 (mkConst ``Description.indexedArray) children entries
    let same ← mkAppM ``Eq.symm #[partitionProof]
    let same ← mkAppM ``congrArg #[mkApp (mkConst ``Description.indexedArray) children, same]
    let proof ← mkAppM ``congrArg #[mkConst ``Bank.leaf, same]
    return (mkApp (mkConst ``Bank.leaf) replacement, proof)
  unless bank.isAppOf ``Bank.branch do throwError "expected the source bank tree"
  let args := bank.getAppArgs
  let split := args[0]!
  let left := args[1]!
  let right := args[2]!
  let scalar ← whnf split
  let some bound := scalar.rawNatLit? | throwError "expected a concrete source bank split"
  if index < bound then
    let (replacement, same) ← replaceArrayPath left index entries partitionProof
    return (mkApp3 (mkConst ``Bank.branch) split replacement right,
      ← branchProof split left right same true)
  else
    let (replacement, same) ← replaceArrayPath right index entries partitionProof
    return (mkApp3 (mkConst ``Bank.branch) split left replacement,
      ← branchProof split left right same false)

/-- The kernel checks the complete bank equality against the original
selected description and the exact scalar partition. -/
elab "repack_source_array " target:ident " in " data:ident " at " index:num
    " with " partition:ident : command => withEnableInfoTree false do
  let target := target.getId
  let data := data.getId
  let partition := partition.getId
  let bank := mkConst (data.str "bank")
  let entries := mkConst (partition.str "entries")
  let partitionProof := mkConst (partition.str "matches")
  let (value, proof) ← liftTermElabM <| replaceArrayPath bank index.getNat entries partitionProof
  let name := target.str "bank"
  let height := getMaxHeight (← getEnv) value + 1
  liftCoreM <| addDecl (.defnDecl {
    name, levelParams := [], type := mkConst ``Bank, value,
    hints := .regular height, safety := .safe })
  modifyEnv (addNoncomputable · name)
  let type ← liftTermElabM <| mkEq (mkConst name) bank
  liftCoreM <| addDecl (.thmDecl {
    name := target.str "eq_original", levelParams := [], type, value := proof })

end Airbender.Setup.SourceBank
