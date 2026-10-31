import Airbender.Proofs.FullUnsigned.SourceCharacterCertificate

namespace Airbender.Setup.SourceCharacters.Tree
open Lean Meta Elab Command
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000
set_option smartUnfolding false

/-- Evaluate the right segment before applying the left segment. -/
def compose (left right : List Char → List Char) (tail : List Char) : List Char :=
  match right tail with
  | [] => left []
  | head :: rest => left (head :: rest)

private theorem compose_eq (left right : List Char → List Char) (tail : List Char) :
    compose left right tail = left (right tail) := by
  unfold compose
  cases right tail <;> rfl

private theorem join (left right : List Char → List Char) (before middle tail : List Char)
    (first : left middle = before) (second : right tail = middle) :
    compose left right tail = before := by
  rw [compose_eq, second, first]

private theorem encoding_unique (characters : List Char) :
    ∀ other : List Char, List.utf8Encode characters = List.utf8Encode other →
      other = characters := by
  intro other same
  apply String.ofList_injective
  apply String.toByteArray_inj.mp
  exact same.symm

private theorem transport {source : String} {before after : List Char}
    (checked : LiteralCharacters source before) (same : before = after) :
    LiteralCharacters source after := by
  rw [← same]
  exact checked

private def chunkSize : Nat := 2048

private def privateName (base : Name) (label : String) : CommandElabM Name := do
  return mkPrivateNameCore (← getMainModule) (base.str label)

private def checkedData (name : Name) (type value : Lean.Expr) : CommandElabM Unit := do
  let height := getMaxHeight (← getEnv) value + 1
  liftCoreM <| addDecl (.defnDecl {
    name, levelParams := [], type, value, hints := .regular height, safety := .safe })
  modifyEnv (addNoncomputable · name)

private def checkedProof (name : Name) (type value : Lean.Expr) : CommandElabM Unit :=
  liftCoreM <| withOptions (Elab.async.set · false) do
    addDecl (.thmDecl { name, levelParams := [], type, value })

private partial def buildTree (target : Name) (parts suffixes : Array Name)
    (first count : Nat) (functionType : Lean.Expr) : CommandElabM (Name × Name) := do
  let before := mkConst suffixes[first]!
  let tail := mkConst suffixes[first + count]!
  if count = 1 then
    let value := mkApp (mkConst parts[first]!) tail
    let type ← liftTermElabM <| mkEq value before
    let proof ← liftTermElabM <| mkEqRefl value
    let name ← privateName target s!"leaf_matches_{first}"
    checkedProof name type proof
    return (parts[first]!, name)
  let half := count / 2
  let (left, firstProof) ← buildTree target parts suffixes first half functionType
  let (right, secondProof) ← buildTree target parts suffixes (first + half) (count - half) functionType
  let name ← privateName target s!"node_{first}_{count}"
  checkedData name functionType (mkApp2 (mkConst ``compose) (mkConst left) (mkConst right))
  let proof := mkAppN (mkConst ``join) #[mkConst left, mkConst right, before,
    mkConst suffixes[first + half]!, tail, mkConst firstProof, mkConst secondProof]
  let type ← liftTermElabM <| mkEq (mkApp (mkConst name) tail) before
  let proofName ← privateName target s!"node_matches_{first}_{count}"
  checkedProof proofName type proof
  return (name, proofName)

/-- Build two equal representations. Each segment and tree join has a
kernel proof. The linked representation supports bounded source intervals. -/
elab "prepare_literal_character_tree " target:ident " from " source:ident : command =>
    withEnableInfoTree false do
  let target := target.getId
  let original ← getConstInfoDefn source.getId
  let .lit (.strVal original) := original.value
    | throwError "expected the original source string literal"
  let characters := original.toList.toArray
  unless characters.size > 0 do throwError "expected a nonempty original source"
  let charType := mkConst ``Char
  let charList := mkApp (mkConst ``List [Level.zero]) charType
  let functionType := mkForall `tail .default charList charList
  let cons := mkApp (mkConst ``List.cons [Level.zero]) charType
  let nil := mkApp (mkConst ``List.nil [Level.zero]) charType
  let ofNat := mkConst ``Char.ofNat
  let mut heads : Std.HashMap Char Lean.Expr := {}
  for character in characters do
    unless heads.contains character do
      heads := heads.insert character (mkApp ofNat (mkRawNatLit character.toNat))
  let count := (characters.size + chunkSize - 1) / chunkSize
  let mut parts : Array Name := #[]
  for first in List.range count do
    let part := characters.extract (first * chunkSize)
      (min characters.size ((first + 1) * chunkSize))
    let body := part.foldr (fun character tail => mkApp2 cons (heads[character]!) tail) (mkBVar 0)
    let name ← privateName target s!"segment_{first}"
    checkedData name functionType (mkLambda `tail .default charList body)
    parts := parts.push name
  let mut suffixes := Array.replicate (count + 1) Name.anonymous
  let endName ← privateName target "characters_end"
  checkedData endName charList nil
  suffixes := suffixes.set! count endName
  for step in List.range count do
    let first := count - 1 - step
    let name ← privateName target s!"characters_{first}"
    checkedData name charList (mkApp (mkConst parts[first]!) (mkConst suffixes[first + 1]!))
    suffixes := suffixes.set! first name
  let (root, same) ← buildTree target parts suffixes 0 count functionType
  let linked := target.str "characters"
  let forced := target.str "forced_characters"
  checkedData linked charList (mkConst suffixes[0]!)
  checkedData forced charList (mkApp (mkConst root) nil)
  let type ← liftTermElabM <| mkEq (mkConst forced) (mkConst linked)
  checkedProof (target.str "forced_eq_characters") type (mkConst same)
  logInfo m!"kernel checked {count} character segments and every tree join"

/-- Check the literal model separately from data generation. The final
certificate uses the proved equality of the two character representations. -/
elab "certify_literal_character_tree " target:ident " from " source:ident : command =>
    withEnableInfoTree false do
  let target := target.getId
  let source := mkConst source.getId
  let forced := mkConst (target.str "forced_characters")
  let linked := mkConst (target.str "characters")
  let type := mkApp2 (mkConst ``LiteralCharacters) source forced
  let proof := mkApp (mkConst ``encoding_unique) forced
  let name ← privateName target "forced_literal_checked"
  checkedProof name type proof
  let type := mkApp2 (mkConst ``LiteralCharacters) source linked
  let proof := mkAppN (mkConst ``transport)
    #[source, forced, linked, mkConst name, mkConst (target.str "forced_eq_characters")]
  checkedProof (target.str "literal_checked") type proof
  logInfo "kernel checked the complete original literal model"

end Airbender.Setup.SourceCharacters.Tree
