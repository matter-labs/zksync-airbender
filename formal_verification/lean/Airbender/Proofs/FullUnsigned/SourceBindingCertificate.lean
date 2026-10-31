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

private theorem interval_of_parts (size : Nat) (before front after : List Char)
    (first : before.take size = front) (last : before.drop size = after) :
    before = front ++ after := by
  rw [← first, ← last]
  exact (List.take_append_drop size before).symm

private partial def explicitList (value : Lean.Expr) : MetaM Lean.Expr := do
  let value := value.consumeMData
  if value.isAppOf ``List.nil || value.isAppOf ``List.cons then return value
  if value.isConst then
    let definition ← getConstInfoDefn value.constName!
    return ← explicitList definition.value
  let expanded ← withTransparency .all <| whnf value
  unless expanded.isAppOf ``List.nil || expanded.isAppOf ``List.cons do
    throwError "expected a retained character suffix"
  return expanded

private partial def literalSegment (value : Lean.Expr) : MetaM (Lean.Expr × Lean.Expr × Nat) := do
  if value.isConst then
    return ← literalSegment (← getConstInfoDefn value.constName!).value
  unless value.isApp && value.appFn!.isConst do
    throwError "expected a retained literal segment application"
  let function := value.appFn!
  let definition ← getConstInfoDefn function.constName!
  let .lam _ _ body _ := definition.value
    | throwError "expected a retained literal segment function"
  let mut body := body
  let mut size := 0
  while body.isAppOf ``List.cons do
    size := size + 1
    body := body.getAppArgs[2]!
  unless body == mkBVar 0 && size > 0 do
    throwError "expected a nonempty literal segment with its supplied tail"
  return (function, value.appArg!, size)

/-- Propose an interval from the existing literal segments. The interval and
its exact tail are checked again by the ordinary kernel equalities below. -/
private def literalFront (before : Lean.Expr) (size : Nat) : MetaM (Lean.Expr × Lean.Expr) := do
  let mut after := before
  let mut remaining := size
  let mut segments : Array Lean.Expr := #[]
  while remaining > 0 do
    let (segment, tail, count) ← literalSegment after
    unless count ≤ remaining do throwError "source interval must end at a literal segment boundary"
    remaining := remaining - count
    segments := segments.push segment
    after := tail
  let nil := mkApp (mkConst ``List.nil [Level.zero]) (mkConst ``Char)
  return (segments.foldr mkApp nil, after)

private theorem identity_continuation (bytes characters : List Char) :
    (bytes = characters) → bytes = characters := id

private theorem continue_interval (original characters before front after rawAfter rawBefore : List Char)
    (previous : before = rawBefore → original = characters)
    (step : before = front ++ after) (matched : front ++ rawAfter = rawBefore) :
    after = rawAfter → original = characters := by
  intro rest
  exact previous (interval_join before front after rawAfter rawBefore step rest matched)

/-- Check every renderer interval and both final empty tails. -/
private def certifySourceBinding (target data source literal bytes bank : Name)
    (chunkSize : Nat) (charactersOnly : Bool) : CommandElabM Unit := do
  unless chunkSize > 0 do throwError "expected a positive source interval size"
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
    let (front, proposedRawAfter) ← if charactersOnly then
      liftTermElabM <| literalFront rawBefore size
      else pure (characterPrefix (characters.extract offset (offset + size)) nil, rawBefore)
    let (after, rawAfter) ← liftTermElabM <|
        withOptions (fun options => options.setBool `smartUnfolding false) <|
        withTransparency .all do
      let mut after := before
      let mut rawAfter := rawBefore
      for _ in List.range size do
        let expanded ← whnf after
        unless expanded.isAppOf ``List.cons do throwError "captured source ended before character {offset}"
        after := expanded.getAppArgs[2]!
        unless charactersOnly do
          let rawExpanded ← explicitList rawAfter
          unless rawExpanded.isAppOf ``List.cons do throwError "literal character data ended early"
          rawAfter := rawExpanded.getAppArgs[2]!
      if charactersOnly then rawAfter := proposedRawAfter
      return (after, rawAfter)
    if part = 0 then liftIO <| IO.eprintln "source binding: first interval evaluated"
    if let some path := progressPath then
      if part % 16 = 0 then liftIO <| IO.FS.writeFile path s!"check cursor at character offset {offset}"
    let suffix ← privateName target s!"source_suffix_{part + 1}"
    checkedData suffix charList after
    if part = 0 then liftIO <| IO.eprintln "source binding: first cursor data checked"
    cursor := mkConst suffix
    rawCursor := rawAfter
    let proposed := mkApp3 (mkConst ``List.append [Level.zero]) charType front cursor
    let intervalType ← liftTermElabM <| mkEq before proposed
    let intervalProof ← if charactersOnly then do
      let amount := mkRawNatLit size
      let prefixName ← privateName target s!"source_prefix_{part}"
      let prefixType ← liftTermElabM <| mkEq
        (mkApp3 (mkConst ``List.take [Level.zero]) charType amount before) front
      let prefixProof ← liftTermElabM <| mkEqRefl front
      checkedProof prefixName prefixType prefixProof
      let suffixName ← privateName target s!"source_drop_{part}"
      let suffixType ← liftTermElabM <| mkEq
        (mkApp3 (mkConst ``List.drop [Level.zero]) charType amount before) cursor
      let suffixProof ← liftTermElabM <| mkEqRefl cursor
      checkedProof suffixName suffixType suffixProof
      pure <| mkAppN (mkConst ``interval_of_parts)
        #[amount, before, front, cursor, mkConst prefixName, mkConst suffixName]
      else liftTermElabM <| mkEqRefl proposed
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
  if charactersOnly then
    logInfo m!"kernel checked all {characters.size} source characters in {count} intervals"
    return
  let proof := mkAppN (mkConst ``source_of_characters)
    #[mkConst source, sourceBytes, rawCharacters, mkConst bytesName,
      mkConst (literal.str "literal_checked")]
  let type ← liftTermElabM <| mkEq (mkConst (data.str "source")) (mkConst source)
  if let some path := progressPath then liftIO <| IO.FS.writeFile path "verify original string equality"
  checkedProof (target.str "source_eq") type proof
  logInfo m!"kernel checked the complete original source-string binding in {count} intervals"

/-- Check the complete source binding with the retained literal certificate. -/
elab "certify_source_string_binding " target:ident " using " data:ident
    " against " source:ident " with " literal:ident
    " bytes " byteLibrary:ident " bank " bankData:ident : command =>
    withEnableInfoTree false do
  certifySourceBinding target.getId data.getId source.getId literal.getId byteLibrary.getId bankData.getId
    chunkSize false

/-- Check the character equality before the independent literal model. -/
elab "certify_source_character_binding " target:ident " using " data:ident
    " against " source:ident " with " literal:ident
    " bytes " byteLibrary:ident " bank " bankData:ident " interval " amount:num : command =>
    withEnableInfoTree false do
  certifySourceBinding target.getId data.getId source.getId literal.getId byteLibrary.getId bankData.getId
    amount.getNat true

/-- Join the two kernel certificates at the original string interface. -/
elab "close_source_string_binding " target:ident " using " data:ident
    " against " source:ident " with " literal:ident : command =>
    withEnableInfoTree false do
  let target := target.getId
  let source := mkConst source.getId
  let data := data.getId
  let literal := literal.getId
  let sourceBytes := mkApp (mkConst ``SourceData.Node.bytes) (mkConst (data.str "root"))
  let characters := mkConst (literal.str "characters")
  let proof := mkAppN (mkConst ``source_of_characters)
    #[source, sourceBytes, characters, mkConst (target.str "bytes_checked"),
      mkConst (literal.str "literal_checked")]
  let type ← liftTermElabM <| mkEq (mkConst (data.str "source")) source
  checkedProof (target.str "source_eq") type proof

end Airbender.Setup.SourceCharacters
