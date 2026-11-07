import Airbender.Proofs.FullUnsigned.SourceIndexPartitions

namespace Airbender.Setup.SourceIndices
open Lean Meta Elab Command
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

/-- Decode the bounded pieces once. The kernel proves the complete list
identity before any source renderer uses the literal indices. -/
elab "certify_source_index_literals " target:ident " from " partition:ident : command =>
    withEnableInfoTree false do
  let target := target.getId
  let partition := partition.getId
  let original := mkConst (partition.str "chunks")
  let flattened ← liftTermElabM <| mkAppM ``List.flatten #[original]
  let values ← liftTermElabM <| withTransparency .all do
    let mut rest := flattened
    let mut values : Array Nat := #[]
    repeat
      let list ← whnf rest
      if list.isAppOf ``List.nil then break
      unless list.isAppOf ``List.cons do throwError "expected partitioned source indices"
      let args := list.getAppArgs
      let value ← whnf args[1]!
      let some value := value.rawNatLit? | throwError "expected one concrete source index"
      values := values.push value
      rest := args[2]!
    return values
  let listType := mkApp (mkConst ``List [Level.zero]) (mkConst ``Nat)
  let mut tail := mkApp (mkConst ``List.nil [Level.zero]) (mkConst ``Nat)
  let count := (values.size + 63) / 64
  for step in List.range count do
    let first := count - 1 - step
    let entries := values.extract (first * 64) (min values.size ((first + 1) * 64))
    let value := entries.foldr (fun entry rest =>
      mkApp3 (mkConst ``List.cons [Level.zero]) (mkConst ``Nat) (mkRawNatLit entry) rest) tail
    let name := mkPrivateNameCore (← getMainModule) (target.str s!"suffix_{first}")
    let height := getMaxHeight (← getEnv) value + 1
    liftCoreM <| addDecl (.defnDecl {
      name, levelParams := [], type := listType, value,
      hints := .regular height, safety := .safe })
    modifyEnv (addNoncomputable · name)
    tail := mkConst name
  let name := target.str "entries"
  let height := getMaxHeight (← getEnv) tail + 1
  liftCoreM <| addDecl (.defnDecl {
    name, levelParams := [], type := listType, value := tail,
    hints := .regular height, safety := .safe })
  modifyEnv (addNoncomputable · name)
  let sameName := mkPrivateNameCore (← getMainModule) (target.str "flattened")
  let type ← liftTermElabM <| mkEq flattened (mkConst name)
  let proof ← liftTermElabM <| mkEqRefl (mkConst name)
  liftCoreM <| addDecl (.thmDecl {name := sameName, levelParams := [], type, value := proof})
  let proof ← liftTermElabM <| mkAppM ``Eq.trans #[mkConst (partition.str "matches"), mkConst sameName]
  let type ← liftTermElabM <| inferType proof
  liftCoreM <| addDecl (.thmDecl {
    name := target.str "matches", levelParams := [], type, value := proof })
  logInfo m!"kernel checked all {values.size} literal source indices"

end Airbender.Setup.SourceIndices
