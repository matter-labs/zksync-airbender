import Airbender.Proofs.FullUnsigned.SourceCharacterCertificate
import Airbender.Proofs.FullUnsigned.SourceByteRenderer

namespace Airbender.Setup.SourceCharacters
open Lean Meta Elab Command
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000
set_option smartUnfolding false

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

private def characterPrefix (characters : Array Char) (tail : Lean.Expr) : Lean.Expr :=
  characters.foldr (fun character rest =>
    mkApp3 (mkConst ``List.cons [Level.zero]) (mkConst ``Char)
      (mkApp (mkConst ``Char.ofNat) (mkRawNatLit character.toNat)) rest) tail

private theorem interval_join (before front after rawAfter rawBefore : List Char)
    (step : before = front ++ after) (rest : after = rawAfter)
    (characters : front ++ rawAfter = rawBefore) : before = rawBefore := by
  rw [step, rest, characters]

private partial def explicitList (value : Lean.Expr) : MetaM Lean.Expr := do
  let value := value.consumeMData
  if value.isAppOf ``List.nil || value.isAppOf ``List.cons then return value
  unless value.isConst do throwError "expected a retained character suffix"
  let definition ← getConstInfoDefn value.constName!
  explicitList definition.value

private theorem identity_continuation (bytes characters : List Char) :
    (bytes = characters) → bytes = characters := id

private theorem continue_interval (original characters before front after rawAfter rawBefore : List Char)
    (previous : before = rawBefore → original = characters)
    (step : before = front ++ after) (matched : front ++ rawAfter = rawBefore) :
    after = rawAfter → original = characters := by
  intro rest
  exact previous (interval_join before front after rawAfter rawBefore step rest matched)

/-- Every interval and both final empty tails enter ordinary kernel checks.
The byte and bank equalities connect the renderer to the original source. -/
elab "certify_source_string_binding " target:ident " using " data:ident
    " against " source:ident " with " literal:ident
    " bytes " bytes:ident " bank " bank:ident : command =>
    withEnableInfoTree false do
  let target := target.getId
  let data := data.getId
  let source := source.getId
  let literal := literal.getId
  let bytes := bytes.getId
  let bank := bank.getId
  let progressPath ← liftIO <| IO.getEnv "AIRBENDER_SOURCE_BINDING_PROGRESS"
  let original ← getConstInfoDefn source
  let .lit (.strVal original) := original.value
    | throwError "expected the original source string literal"
  let characters := original.toList.toArray
  let charType := mkConst ``Char
  let charList := mkApp (mkConst ``List [Level.zero]) charType
  let nil := mkApp (mkConst ``List.nil [Level.zero]) charType
  let strings := mkConst (data.str "text")
  let tokens := mkConst (data.str "token")
  let originalBank := mkConst (data.str "bank")
  let candidate := mkConst (bank.str "bank")
  let stringBytes := mkConst (bytes.str "text_bytes")
  let numberBytes := mkConst (bytes.str "token_bytes")
  let fuel := mkApp (mkConst ``Nat.succ) (mkConst (data.str "fuel"))
  let index := mkConst (data.str "rootIndex")
  let rendered := mkAppN (mkConst ``Bytes.byteRender)
    #[stringBytes, numberBytes, candidate, fuel, index, nil]
  let rawCharacters := mkConst (literal.str "characters")
  let mut cursor := rendered
  let mut rawCursor := rawCharacters
  let mut continuation := mkApp2 (mkConst ``identity_continuation) rendered rawCharacters
  liftIO <| IO.eprintln "source binding: renderer and original character data selected"
  let count := (characters.size + chunkSize - 1) / chunkSize
  for part in List.range count do
    let offset := part * chunkSize
    if let some path := progressPath then
      if part % 16 = 0 then
        liftIO <| IO.FS.writeFile path s!"advance interval {part}; character offset {offset} of {characters.size}"
    let size := min chunkSize (characters.size - offset)
    if part = 0 then liftIO <| IO.eprintln "source binding: advance first interval"
    let before := cursor
    let rawBefore := rawCursor
    let (after, rawAfter) ← liftTermElabM <|
        withOptions (fun options => options.setBool `smartUnfolding false) <|
        withTransparency .all do
      let mut after := before
      let mut rawAfter := rawBefore
      for _ in List.range size do
        let expanded ← whnf after
        unless expanded.isAppOf ``List.cons do throwError "captured source ended before character {offset}"
        after := expanded.getAppArgs[2]!
        let rawExpanded ← explicitList rawAfter
        unless rawExpanded.isAppOf ``List.cons do throwError "literal character data ended early"
        rawAfter := rawExpanded.getAppArgs[2]!
      return (after, rawAfter)
    if part = 0 then liftIO <| IO.eprintln "source binding: first interval evaluated"
    if let some path := progressPath then
      if part % 16 = 0 then liftIO <| IO.FS.writeFile path s!"check cursor at character offset {offset}"
    let suffix ← privateName target s!"source_suffix_{part + 1}"
    checkedData suffix charList after
    if part = 0 then liftIO <| IO.eprintln "source binding: first cursor data checked"
    cursor := mkConst suffix
    rawCursor := rawAfter
    let front := characterPrefix (characters.extract offset (offset + size)) nil
    let proposed := mkApp3 (mkConst ``List.append [Level.zero]) charType front cursor
    let intervalType ← liftTermElabM <| mkEq before proposed
    let intervalProof ← liftTermElabM <| mkEqRefl proposed
    let interval ← privateName target s!"source_interval_{part}"
    checkedProof interval intervalType intervalProof
    if part = 0 then liftIO <| IO.eprintln "source binding: first interval equality checked"
    let matched ← liftTermElabM <| mkEqRefl rawBefore
    let proof := mkAppN (mkConst ``continue_interval)
      #[rendered, rawCharacters, before, front, cursor, rawAfter, rawBefore,
        continuation, mkConst interval, matched]
    let type ← liftTermElabM do
      mkArrow (← mkEq cursor rawAfter) (← mkEq rendered rawCharacters)
    let name ← privateName target s!"continued_{part}"
    checkedProof name type proof
    continuation := mkConst name
    if part % 256 = 0 then
      liftIO do
        let output ← IO.getStderr
        output.putStrLn s!"kernel checked source characters through {offset + size} of {characters.size}"
        output.flush
  if let some path := progressPath then liftIO <| IO.FS.writeFile path "all intervals checked; verify final tails"
  let endName ← privateName target "source_end"
  let endType ← liftTermElabM <| mkEq cursor rawCursor
  let endProof ← liftTermElabM <| mkEqRefl nil
  checkedProof endName endType endProof
  let renderedProof := mkApp continuation (mkConst endName)
  let sourceBytes := mkApp (mkConst ``SourceData.Node.bytes) (mkConst (data.str "root"))
  let bytesName := target.str "bytes_checked"
  let bytesType ← liftTermElabM <| mkEq sourceBytes rawCharacters
  let bytesProof ← liftTermElabM <| mkAppM ``Eq.trans
    #[mkAppN (mkConst ``Bytes.byteRender_bytes_of_bank_eq)
      #[strings, tokens, originalBank, candidate, stringBytes, numberBytes,
        mkConst (bank.str "eq_original"), mkConst (bytes.str "text_bytes_eq"),
        mkConst (bytes.str "token_bytes_eq"), fuel, index], renderedProof]
  if let some path := progressPath then liftIO <| IO.FS.writeFile path "verify complete source bytes theorem"
  checkedProof bytesName bytesType bytesProof
  let proof := mkAppN (mkConst ``source_of_characters)
    #[mkConst source, sourceBytes, rawCharacters, mkConst bytesName,
      mkConst (literal.str "literal_checked")]
  let type ← liftTermElabM <| mkEq (mkConst (data.str "source")) (mkConst source)
  if let some path := progressPath then liftIO <| IO.FS.writeFile path "verify original string equality"
  checkedProof (target.str "source_eq") type proof
  logInfo m!"kernel checked the complete original source-string binding in {count} intervals"

end Airbender.Setup.SourceCharacters
