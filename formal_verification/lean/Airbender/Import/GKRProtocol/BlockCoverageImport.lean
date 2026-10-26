import Airbender.Import.GKRProtocol.BlockPartsImport

namespace Airbender.Compiler.BlockCoverageImport
open Lean Elab Command
set_option warningAsError true

private def listType : Lean.Expr := mkApp (mkConst ``List [Level.zero]) (mkConst ``Setup.Block)
private def appendLists (operation left right : Lean.Expr) : Lean.Expr :=
  mkApp2 operation left right
private def literal (blocks : Array Lean.Expr) : Lean.Expr :=
  blocks.foldr (fun block rest => mkApp3 (mkConst ``List.cons [Level.zero])
    (mkConst ``Setup.Block) block rest)
    (mkApp (mkConst ``List.nil [Level.zero]) (mkConst ``Setup.Block))

private def defineList (name : Name) (value : Lean.Expr) : CommandElabM Lean.Expr := do
  liftCoreM <| addDecl (.defnDecl {
    name, levelParams := [], type := listType, value,
    hints := .regular (getMaxHeight (← getEnv) value + 1), safety := .safe })
  modifyEnv (addNoncomputable · name)
  liftCoreM <| Lean.enableRealizationsForConst name
  return mkConst name

private def proveEquality (name : Name) (left right proof : Lean.Expr) : CommandElabM Lean.Expr := do
  let type ← liftTermElabM <| Meta.mkEq left right
  liftCoreM <| addDecl (.thmDecl {name, levelParams := [], type, value := proof})
  return mkConst name

private partial def arraySize (value : Lean.Expr) : CommandElabM Nat := do
  let value := value.consumeMData
  if let .const name _ := value then return ← arraySize (← getConstInfoDefn name).value
  if value.getAppFn.isConstOf ``Array.append then
    let args := value.getAppArgs
    return (← arraySize args[1]!) + (← arraySize args[2]!)
  unless value.getAppFn.isConstOf ``List.toArray do throwError "expected a literal block array"
  return (← Setup.Proofs.literalList value.getAppArgs[1]!).size

structure State where
  serial : Nat := 0
  position : Nat := 0
  pieces : Array (Array Lean.Expr)
  operation : Lean.Expr

private def nextName (owner : Name) (stem : String) : StateT State CommandElabM Name := do
  let serial := (← get).serial
  modify fun state => {state with serial := serial + 1}
  return owner ++ Name.mkSimple s!"{stem}{serial}"

private partial def cover (owner : Name) (ends : Array Nat) (value : Lean.Expr) :
    StateT State CommandElabM (Lean.Expr × Lean.Expr) := do
  let value := value.consumeMData
  let operation := (← get).operation
  if let .const name _ := value then return ← cover owner ends (← getConstInfoDefn name).value
  if value.getAppFn.isConstOf ``Array.append then
    let args := value.getAppArgs
    let (left, first) ← cover owner ends args[1]!
    let (right, second) ← cover owner ends args[2]!
    let lhs := mkApp2 (mkConst ``Array.toList [Level.zero]) (mkConst ``Setup.Block) value
    let rhs := appendLists operation left right
    let proof ← liftM <| liftTermElabM do
      let initial := mkApp3 (mkConst ``Array.toList_append [Level.zero]) (mkConst ``Setup.Block) args[1]! args[2]!
      let joined ← Meta.mkAppM ``congrArg₂
        #[operation, first, second]
      Meta.mkAppM ``Eq.trans #[initial, joined]
    let result ← liftM <| proveEquality (← nextName owner "node") lhs rhs proof
    return (rhs, result)
  unless value.getAppFn.isConstOf ``List.toArray do throwError "expected a literal block-array leaf"
  let blocks ← Setup.Proofs.literalList value.getAppArgs[1]!
  let blockStart := (← get).position
  let mut segments := #[]
  let mut partStart := 0
  for part in [:ends.size] do
    let finish := ends[part]!
    let lo := max blockStart partStart
    let hi := min (blockStart + blocks.size) finish
    if lo < hi then
      let segment ← liftM <| defineList (← nextName owner "segment") (literal (blocks.extract (lo - blockStart) (hi - blockStart)))
      segments := segments.push segment
      modify fun state => {state with pieces := state.pieces.modify part (·.push segment)}
    partStart := finish
  modify fun state => {state with position := blockStart + blocks.size}
  let rhs := segments.foldr (appendLists operation) (literal #[])
  let lhs := mkApp2 (mkConst ``Array.toList [Level.zero]) (mkConst ``Setup.Block) value
  let proof := mkApp2 (mkConst ``List.toList_toArray [Level.zero]) (mkConst ``Setup.Block) value.getAppArgs[1]!
  let result ← liftM <| proveEquality (← nextName owner "leaf") lhs rhs proof
  return (rhs, result)

/-- Compose exact literal leaf equalities with append congruence. The command
only supplies proof terms: every source leaf and every claimed part is checked
by the kernel, with no whole-column evaluation or asserted coverage axiom. -/
elab "column_parts_cover " name:ident " from " column:term " parts " "[" parts:ident,* "]" : command => do
  let owner := (← getCurrNamespace) ++ name.getId
  let expanded ← liftTermElabM do
    let term ← Term.elabTermEnsuringType column (mkConst ``Setup.Column)
    Meta.withTransparency .all (Meta.whnf term)
  unless expanded.getAppFn.isConstOf ``Setup.Column.mk do throwError "expected an imported column"
  let actual := expanded.getAppArgs[0]!
  let mut ends := #[]
  let mut total := 0
  let mut resolved := #[]
  for part in parts.getElems do
    let constant ← resolveGlobalConstNoOverload part
    let info ← getConstInfoDefn constant
    let blocks ← Setup.Proofs.literalList info.value
    total := total + blocks.size
    ends := ends.push total
    resolved := resolved.push constant
  unless (← arraySize actual) == total do throwError "column parts omit or duplicate blocks"
  let operation ← liftTermElabM do
    let term ← Term.elabTerm (← `((fun (left right : List Setup.Block) => left ++ right))) none
    instantiateMVars term
  let ((rootValue, root), final) ← (cover owner ends actual).run {pieces := Array.replicate resolved.size #[], operation}
  unless final.position == total do throwError "column leaf coverage changed"
  let mut shapes := #[]
  for index in [:resolved.size] do
    let left := mkConst resolved[index]!
    let right := final.pieces[index]!.foldr (appendLists operation) (literal #[])
    let proof ← liftTermElabM <| Meta.mkEqRefl left
    let shapeName := owner ++ Name.mkSimple s!"part{index}"
    let _ ← proveEquality shapeName left right proof
    shapes := shapes.push (mkIdent shapeName)
  let rootViewName := owner ++ `view
  let rootView ← defineList rootViewName rootValue
  let rootLeft ← liftTermElabM do
    let type ← Meta.inferType root
    return type.getAppArgs[1]!
  let rootCheckedName := owner ++ `checked
  let _ ← proveEquality rootCheckedName rootLeft rootView root
  let rootName := mkIdent rootCheckedName
  let rootViewIdent := mkIdent rootViewName
  let flatParts := parts.getElems.map fun part => (part : TSyntax `term)
  let command ← `(theorem $name : ($column).blocks.toList = ([$flatParts,*] : List (List Setup.Block)).flatten := by
    trans $rootViewIdent:ident
    · exact $rootName:ident
    · simp only [$rootViewIdent:ident, $[$shapes:ident],*, List.flatten_cons, List.flatten_nil, List.append_assoc, List.append_nil])
  withEnableInfoTree false (elabCommand command)
  if (← get).messages.hasErrors then throwAbortCommand

end Airbender.Compiler.BlockCoverageImport
