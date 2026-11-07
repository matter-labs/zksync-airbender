import Lean

namespace Airbender.Setup.SourceCharacters
open Lean Meta Elab Command
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000
set_option smartUnfolding false

/-- Read the character model through the primitive string recursor. This
keeps the kernel comparison on character lists instead of byte-array loops. -/
def LiteralCharacters (source : String) (characters : List Char) : Prop :=
  @String.rec (fun _ : String => Prop)
    (fun bytes _valid =>
      ∀ other : List Char, bytes = List.utf8Encode other → other = characters)
    source

private theorem encoding_unique (characters : List Char) :
    ∀ other : List Char, List.utf8Encode characters = List.utf8Encode other →
      other = characters := by
  intro other same
  apply String.ofList_injective
  apply String.toByteArray_inj.mp
  exact same.symm

theorem literal_characters_sound {source : String} {characters : List Char}
    (checked : LiteralCharacters source characters) : String.ofList characters = source := by
  cases source with
  | ofByteArray bytes valid =>
    cases valid with
    | intro original same =>
      have equal : original = characters := checked original same
      subst original
      apply String.toByteArray_inj.mp
      exact same.symm

theorem source_of_characters (source : String) (bytes characters : List Char)
    (same : bytes = characters) (checked : LiteralCharacters source characters) :
    String.ofList bytes = source := by
  rw [same]
  exact literal_characters_sound checked

private def chunkSize : Nat := 256

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

private def rawCharacters (source : Name) : CommandElabM (Array Char) := do
  let definition ← getConstInfoDefn source
  let .lit (.strVal value) := definition.value
    | throwError "expected the original source string literal"
  return value.toList.toArray

private def characterPrefix (characters : Array Char) (tail : Lean.Expr) : Lean.Expr :=
  characters.foldr (fun character rest =>
    mkApp3 (mkConst ``List.cons [Level.zero]) (mkConst ``Char)
      (mkApp (mkConst ``Char.ofNat) (mkRawNatLit character.toNat)) rest) tail

/-- The command proposes safe data and ordinary proof terms. The kernel
checks the literal model. Character tails share bounded suffix declarations. -/
elab "certify_literal_characters " target:ident " from " source:ident : command =>
    withEnableInfoTree false do
  let target := target.getId
  let source := source.getId
  let characters ← rawCharacters source
  let charList := mkApp (mkConst ``List [Level.zero]) (mkConst ``Char)
  let mut tail := mkApp (mkConst ``List.nil [Level.zero]) (mkConst ``Char)
  let count := (characters.size + chunkSize - 1) / chunkSize
  for step in List.range count do
    let first := count - 1 - step
    let name ← privateName target s!"characters_{first}"
    let part := characters.extract (first * chunkSize)
      (min characters.size ((first + 1) * chunkSize))
    checkedData name charList (characterPrefix part tail)
    tail := mkConst name
  let data := target.str "characters"
  checkedData data charList tail
  let type := mkApp2 (mkConst ``LiteralCharacters) (mkConst source) (mkConst data)
  let proof := mkApp (mkConst ``encoding_unique) (mkConst data)
  checkedProof (target.str "literal_checked") type proof
  logInfo m!"kernel checked {characters.size} literal characters in {count} shared intervals"

end Airbender.Setup.SourceCharacters
