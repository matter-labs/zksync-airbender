import Airbender.Proofs.FullUnsigned.SourceCharacterRenderer
import Lean
open Lean Meta Elab Command
open Airbender.Setup Airbender.Setup.SourceData Airbender.Setup.SourceBank
open Airbender.Setup.SourceCharacters.Renderer
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000
namespace Airbender.Setup.SourceCharacters.Bytes
private theorem choose_bytes {α : Type} (decode : α → List Char)
    (condition : Prop) [Decidable condition] {left right : α} {a b : List Char}
    (l : a = decode left) (r : b = decode right) :
    (if condition then a else b) = decode (if condition then left else right) := by
  split <;> assumption

private partial def elements (value : Lean.Expr) : MetaM (Array Lean.Expr) := do
  let value ← whnf value
  if value.isAppOf ``List.nil then return #[]
  unless value.isAppOf ``List.cons do throwError "expected a literal library list"
  let args := value.getAppArgs
  return #[args[1]!] ++ (← elements args[2]!)
private def checkedData (name : Name) (type value : Lean.Expr) : CommandElabM Unit := do
  let height := getMaxHeight (← getEnv) value + 1
  liftCoreM <| addDecl (.defnDecl {
    name := name, levelParams := [], type := type, value := value,
    hints := .regular height, safety := .safe })
  modifyEnv (addNoncomputable · name)
private def checkedProof (name : Name) (type value : Lean.Expr) : CommandElabM Unit :=
  liftCoreM <| addDecl (.thmDecl {name := name, levelParams := [], type := type, value := value})

private def proposedCharacters (bytes : Lean.Expr) : MetaM Lean.Expr := withTransparency .all do
  let mut cursor := bytes
  let mut characters : Array Nat := #[]
  repeat
    let expanded ← whnf cursor
    if expanded.isAppOf ``List.nil then break
    unless expanded.isAppOf ``List.cons do throwError "expected source characters"
    let args := expanded.getAppArgs
    let scalar ← whnf (mkApp (mkConst ``Char.toNat) args[1]!)
    let some value := scalar.rawNatLit? | throwError "expected one concrete character"
    characters := characters.push value
    cursor := args[2]!
  return characters.foldr (fun character tail =>
    mkApp3 (mkConst ``List.cons [Level.zero]) (mkConst ``Char)
      (mkApp (mkConst ``Char.ofNat) (mkRawNatLit character)) tail)
    (mkApp (mkConst ``List.nil [Level.zero]) (mkConst ``Char))

private partial def transformed (body : Lean.Expr) (entries : Std.HashMap Name (Name × Name)) : MetaM Lean.Expr := do
  let body := body.consumeMData
  if body.isConst then
    let some (data, _) := entries[body.constName!]? | throwError "unretained literal leaf {body.constName!}"
    return mkConst data
  unless body.isAppOf ``ite do throwError "expected the source selector tree"
  let args := body.getAppArgs
  return mkAppN body.getAppFn #[mkApp (mkConst ``List [Level.zero]) (mkConst ``Char),
    args[1]!, args[2]!, ← transformed args[3]! entries, ← transformed args[4]! entries]

private partial def selectorProof (decode body : Lean.Expr) (entries : Std.HashMap Name (Name × Name)) : MetaM Lean.Expr := do
  let body := body.consumeMData
  if body.isConst then
    let some (_, proof) := entries[body.constName!]? | throwError "unproved literal leaf"
    return mkConst proof
  unless body.isAppOf ``ite do throwError "expected the source selector tree"
  let args := body.getAppArgs
  mkAppM ``choose_bytes #[decode, args[1]!, ← selectorProof decode args[3]! entries,
    ← selectorProof decode args[4]! entries]

private def certifyLibrary (base data : Name) (library selector decoder : String) : CommandElabM Unit := do
  let decode := mkConst (if decoder == "string" then ``SourceData.stringBytes else ``SourceData.NumberToken.bytes)
  let values ← liftTermElabM <| elements (mkConst (data.str library))
  let charList := mkApp (mkConst ``List [Level.zero]) (mkConst ``Char)
  let mut entries : Std.HashMap Name (Name × Name) := {}
  for i in List.range values.size do
    let value := values[i]!
    let original := mkApp decode value
    let proposed ← liftTermElabM <| proposedCharacters original
    let name := mkPrivateNameCore (← getMainModule) (base.str s!"{selector}_bytes_{i}")
    checkedData name charList proposed
    let proofName := mkPrivateNameCore (← getMainModule) (base.str s!"{selector}_bytes_{i}_eq")
    let type ← liftTermElabM <| mkEq (mkConst name) original
    let proof ← liftTermElabM <| mkEqRefl (mkConst name)
    checkedProof proofName type proof
    entries := entries.insert value.constName! (name, proofName)
  let selected := mkConst (data.str selector)
  let definition ← getConstInfoDefn selected.constName!
  let (value, proof) ← liftTermElabM do
    withLocalDeclD `index (mkConst ``Nat) fun index => do
      let body := (mkApp definition.value index).headBeta
      let output ← transformed body entries
      let value ← mkLambdaFVars #[index] output
      let proof ← mkLambdaFVars #[index] (← selectorProof decode body entries)
      return (value, proof)
  let name := base.str (selector ++ "_bytes")
  let functionType ← liftTermElabM <| mkArrow (mkConst ``Nat) charList
  checkedData name functionType value
  let type ← liftTermElabM do
    withLocalDeclD `index (mkConst ``Nat) fun index => do
      mkForallFVars #[index] (← mkEq (mkApp (mkConst name) index) (mkApp decode (mkApp selected index)))
  checkedProof (base.str (selector ++ "_bytes_eq")) type proof
  liftIO <| IO.println s!"PASS {values.size} retained {selector} byte encodings"


/-- Every literal encoding has an ordinary kernel equality proof. The selector
proof covers every index, including its original default branch. -/
elab "certify_source_byte_encodings " target:ident " using " data:ident : command =>
    withEnableInfoTree false do
  certifyLibrary target.getId data.getId "strings" "text" "string"
  certifyLibrary target.getId data.getId "tokens" "token" "number"

end Airbender.Setup.SourceCharacters.Bytes
