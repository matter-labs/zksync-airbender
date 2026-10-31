import Airbender.Import.SetupEmbed
import Lean.AddDecl

namespace Airbender.Setup.Proofs
open Lean Elab Command

partial def literalList (value : Lean.Expr) : CommandElabM (Array Lean.Expr) := do
  let value := value.consumeMData
  if let .letE _ _ rhs body _ := value then return ← literalList (body.instantiate1 rhs)
  if value.getAppFn.isConstOf ``List.nil then return #[]
  if let .const name _ := value then return ← literalList (← getConstInfoDefn name).value
  if value.getAppFn.isConstOf ``List.map then
    let args := value.getAppArgs
    unless args.size == 4 do throwError "unexpected imported block-map arity"
    return (← literalList args[3]!).map (mkApp args[2]!)
  unless value.getAppFn.isConstOf ``List.cons do throwError "expected imported literal block list"
  let args := value.getAppArgs
  unless args.size == 3 do throwError "unexpected imported block-list arity"
  return #[args[1]!] ++ (← literalList args[2]!)

partial def literalArray (value : Lean.Expr) : CommandElabM (Array Lean.Expr) := do
  let value := value.consumeMData
  if value.getAppFn.isConstOf ``Array.append then
    let args := value.getAppArgs
    unless args.size == 3 do throwError "unexpected imported array-append arity"
    return (← literalArray args[1]!) ++ (← literalArray args[2]!)
  unless value.getAppFn.isConstOf ``List.toArray do throwError "expected imported literal block array"
  let args := value.getAppArgs
  unless args.size == 2 do throwError "unexpected imported block-array arity"
  literalList args[1]!

partial def balancedArray (values : Array Lean.Expr) : Lean.Expr :=
  let elemType := mkConst ``Airbender.Setup.Block
  if values.size ≤ 64 then
    let list := values.foldr (fun item rest =>
      mkApp3 (mkConst ``List.cons [Level.zero]) elemType item rest)
      (mkApp (mkConst ``List.nil [Level.zero]) elemType)
    mkApp2 (mkConst ``List.toArray [Level.zero]) elemType list
  else
    mkApp3 (mkConst ``Array.append [Level.zero]) elemType
      (balancedArray (values.extract 0 (values.size / 2)))
      (balancedArray (values.extract (values.size / 2) values.size))

/-- Name a literal slice of the existing imported block expressions. The
    command supplies proof data only; reconstruction and semantic equality are proved
    separately by the kernel. No block value or table formula is invented. -/
elab "column_blocks_slice " name:ident " from " column:ident
    " block_start " start:num " block_count " count:num : command => do
  let sourceName ← resolveGlobalConstNoOverload column
  let info ← getConstInfoDefn sourceName
  unless info.type.isConstOf ``Airbender.Setup.Column &&
      info.value.getAppFn.isConstOf ``Airbender.Setup.Column.mk do
    throwError "block slice requires an imported literal Column"
  let blocks ← literalArray info.value.getAppArgs[0]!
  let first := start.getNat
  let last := first + count.getNat
  unless first ≤ last && last ≤ blocks.size do throwError "imported block slice is out of bounds"
  let elemType := mkConst ``Airbender.Setup.Block
  let type := mkApp (mkConst ``Array [Level.zero]) elemType
  let selected := blocks.extract first last
  let value := balancedArray selected
  let height := getMaxHeight (← getEnv) value + 1
  let fullName := (← getCurrNamespace) ++ name.getId
  liftCoreM <| addDecl (.defnDecl {
    name := fullName, levelParams := [], type, value,
    hints := .regular height, safety := .safe })
  modifyEnv (addNoncomputable · fullName)

theorem getFromBlocks_common (front left right : List Airbender.Setup.Block)
    (same : ∀ n, Airbender.Setup.getFromBlocks left n = Airbender.Setup.getFromBlocks right n)
    (n : Nat) : Airbender.Setup.getFromBlocks (front ++ left) n =
      Airbender.Setup.getFromBlocks (front ++ right) n := by
  induction front generalizing n with
  | nil => exact same n
  | cons block rest ih =>
    simp only [List.cons_append, Airbender.Setup.getFromBlocks]
    split
    · rfl
    · exact ih _

end Airbender.Setup.Proofs
