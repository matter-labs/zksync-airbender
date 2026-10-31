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
  if value.getAppFn.isConstOf ``List.take || value.getAppFn.isConstOf ``List.drop then
    let args := value.getAppArgs
    unless args.size == 3 do throwError "unexpected imported list-view arity"
    let scalar ← liftTermElabM <| Meta.whnf args[1]!
    let .lit (.natVal count) := scalar | throwError "imported list view requires a literal index"
    let elements ← literalList args[2]!
    if value.getAppFn.isConstOf ``List.take then return elements.extract 0 (min count elements.size)
    return elements.extract (min count elements.size) elements.size
  if value.getAppFn.isConstOf ``List.append then
    let args := value.getAppArgs
    unless args.size == 3 do throwError "unexpected imported list-append arity"
    return (← literalList args[1]!) ++ (← literalList args[2]!)
  if value.getAppFn.isConstOf ``HAppend.hAppend then
    let args := value.getAppArgs
    unless args.size == 6 do throwError "unexpected imported append-instance arity"
    return (← literalList args[4]!) ++ (← literalList args[5]!)
  unless value.getAppFn.isConstOf ``List.cons do
    let reduced ← liftTermElabM <| Meta.withTransparency .all <| Meta.whnf value
    if reduced == value then throwError "expected imported literal block list"
    return ← literalList reduced
  let args := value.getAppArgs
  unless args.size == 3 do throwError "unexpected imported block-list arity"
  return #[args[1]!] ++ (← literalList args[2]!)

private partial def appendView (value : Lean.Expr) : CommandElabM (Option (Lean.Expr × Lean.Expr)) := do
  let value := value.consumeMData
  if value.getAppFn.isConstOf ``List.append then
    let args := value.getAppArgs
    return some (args[1]!, args[2]!)
  if value.getAppFn.isConstOf ``HAppend.hAppend then
    let args := value.getAppArgs
    return some (args[4]!, args[5]!)
  if let .const name _ := value then
    if let .defnInfo info ← getConstInfo name then return ← appendView info.value
  return none

private def appendBlocks (left right : Lean.Expr) : Lean.Expr :=
  mkApp3 (mkConst ``List.append [Level.zero]) (mkConst ``Airbender.Setup.Block) left right

private def typedEquality (left right proof : Lean.Expr) : CommandElabM Lean.Expr := do
  let type ← liftTermElabM <| Meta.mkEq left right
  return .letE `boundedBinding type proof (.bvar 0) false

private partial def splitList (value : Lean.Expr) (first : Nat) :
    CommandElabM (Lean.Expr × Lean.Expr × Lean.Expr) := do
  let element := mkConst ``Airbender.Setup.Block
  let empty := mkApp (mkConst ``List.nil [Level.zero]) element
  let size := (← literalList value).size
  if first == 0 then
    let proof ← liftTermElabM <| Meta.mkEqSymm (mkApp2 (mkConst ``List.nil_append [Level.zero]) element value)
    return (empty, value, ← typedEquality value (appendBlocks empty value) proof)
  if size ≤ first then
    let proof ← liftTermElabM <| Meta.mkEqSymm (mkApp2 (mkConst ``List.append_nil [Level.zero]) element value)
    return (value, empty, ← typedEquality value (appendBlocks value empty) proof)
  if let some (left, right) ← appendView value then
    let width := (← literalList left).size
    if first == width then
      let proof ← liftTermElabM <| Meta.mkEqRefl value
      return (left, right, ← typedEquality value (appendBlocks left right) proof)
    if first < width then
      let (front, tail, proof) ← splitList left first
      let result ← liftTermElabM do
        let operation ← Meta.mkLambdaFVars #[] (mkApp (mkConst ``List.append [Level.zero]) element)
        let rightProof ← Meta.mkEqRefl right
        let joined ← Meta.mkCongr (← Meta.mkCongrArg operation proof) rightProof
        let assoc := mkApp4 (mkConst ``List.append_assoc [Level.zero]) element front tail right
        Meta.mkEqTrans joined assoc
      let rest := appendBlocks tail right
      return (front, rest, ← typedEquality value (appendBlocks front rest) result)
    else
      let (front, tail, proof) ← splitList right (first - width)
      let result ← liftTermElabM do
        let operation := mkApp2 (mkConst ``List.append [Level.zero]) element left
        let joined ← Meta.mkCongrArg operation proof
        let assoc := mkApp4 (mkConst ``List.append_assoc [Level.zero]) element left front tail
        Meta.mkEqTrans joined (← Meta.mkEqSymm assoc)
      let initial := appendBlocks left front
      return (initial, tail, ← typedEquality value (appendBlocks initial tail) result)
  let front := mkApp3 (mkConst ``List.take [Level.zero]) element (mkNatLit first) value
  let tail := mkApp3 (mkConst ``List.drop [Level.zero]) element (mkNatLit first) value
  let proof ← liftTermElabM <| Meta.mkEqSymm
    (mkApp3 (mkConst ``List.take_append_drop [Level.zero]) element (mkNatLit first) value)
  return (front, tail, ← typedEquality value (appendBlocks front tail) proof)

/-- Compose bounded conversions. The kernel checks every typed local equality. -/
partial def listEqualityProof (left right : Lean.Expr) : CommandElabM Lean.Expr := do
  if let some (first, second) ← appendView left then
    let width := (← literalList first).size
    let (rightFirst, rightSecond, partition) ← splitList right width
    let firstProof ← listEqualityProof first rightFirst
    let secondProof ← listEqualityProof second rightSecond
    let result ← liftTermElabM do
      let operation := mkApp (mkConst ``List.append [Level.zero]) (mkConst ``Airbender.Setup.Block)
      let joined ← Meta.mkCongr (← Meta.mkCongrArg operation firstProof) secondProof
      Meta.mkEqTrans joined (← Meta.mkEqSymm partition)
    typedEquality left right result
  else
    let proof ← liftTermElabM <| Meta.mkEqRefl left
    typedEquality left right proof

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
