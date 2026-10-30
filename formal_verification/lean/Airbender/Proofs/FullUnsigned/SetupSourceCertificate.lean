import Lean
import Airbender.Import.SetupSourceBindings
import Airbender.Proofs.FullUnsigned.SetupSourceRLE
namespace Airbender.Setup.SourceBankCertificate

open Lean Meta Elab Command
open Airbender.Setup Airbender.Setup.SourceProofs
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000
private theorem chooseString (condition : Prop) [Decidable condition]
    {left right : String} (a : check_string left = true) (b : check_string right = true) :
    check_string (if condition then left else right) = true := by
  split <;> assumption

private partial def elements (value : Lean.Expr) : MetaM (Array Lean.Expr) := do
  let value ← whnf value
  if value.isAppOf ``List.nil then return #[]
  unless value.isAppOf ``List.cons do throwError "expected a concrete source metadata list"
  let args := value.getAppArgs
  return #[args[1]!] ++ (← elements args[2]!)

/-- The command proposes ordinary theorem terms. The kernel checks each term. -/
private def addProof (name : Name) (type value : Lean.Expr) : CommandElabM Unit :=
  liftCoreM <| withOptions (Elab.async.set · false) do
    addDecl (.thmDecl { name, levelParams := [], type, value })

private def localName (base : Name) (label : String) : CommandElabM Name := do
  return mkPrivateNameCore (← getMainModule) (base.str label)

private partial def branchProof (body : Lean.Expr) (proved : Std.HashMap Name Name) (chooser : Name) : MetaM Lean.Expr := do
  let body := body.consumeMData
  if !body.isAppOf ``ite && body.getAppFn.isConst then
    let some proof := proved[body.getAppFn.constName!]?
      | throwError "source selector refers to an unproved entry: {body.getAppFn.constName!}"
    return mkConst proof
  unless body.isAppOf ``ite do throwError "source selector is not a constant or a conditional"
  let args := body.getAppArgs
  let left ← branchProof args[3]! proved chooser
  let right ← branchProof args[4]! proved chooser
  mkAppM chooser #[args[1]!, left, right]

private theorem chooseNumber (condition : Prop) [Decidable condition]
    {left right : SourceData.NumberToken}
    (a : check_number_token left = true) (b : check_number_token right = true) :
    check_number_token (if condition then left else right) = true := by
  split <;> assumption

private def libraryProof (selector : Lean.Expr) (proved : Std.HashMap Name Name)
    (checker chooser : Name) : MetaM (Lean.Expr × Lean.Expr) := do
  let .defnInfo definition ← getConstInfo selector.constName!
    | throwError "source library must have a definition"
  withLocalDeclD `index (mkConst ``Nat) fun index => do
    let applied := mkApp selector index
    let body := (mkApp definition.value index).headBeta
    let value ← branchProof body proved chooser
    let property ← mkEq (← mkAppM checker #[applied]) (mkConst ``Bool.true)
    return (← mkForallFVars #[index] property, ← mkLambdaFVars #[index] value)

elab "certify_source_bank " base:ident " using " data:ident : command => withEnableInfoTree false do
  let base := base.getId
  let data := data.getId
  let strings ← liftTermElabM <| elements (mkConst (data.str "strings"))
  let tokens ← liftTermElabM <| elements (mkConst (data.str "tokens"))
  let mut stringChecks : Std.HashMap Name Name := {}
  let mut tokenChecks : Std.HashMap Name Name := {}
  for index in [:strings.size] do
    let entry := strings[index]!
    let name ← localName base s!"string_{index}"
    let type ← liftTermElabM do mkEq (← mkAppM ``check_string #[entry]) (mkConst ``Bool.true)
    let proof ← liftTermElabM <| mkEqRefl (mkConst ``Bool.true)
    addProof name type proof
    stringChecks := stringChecks.insert entry.constName! name
  for index in [:tokens.size] do
    let entry := tokens[index]!
    let name ← localName base s!"number_{index}"
    let type ← liftTermElabM do mkEq (← mkAppM ``check_number_token #[entry]) (mkConst ``Bool.true)
    let proof ← liftTermElabM <| mkEqRefl (mkConst ``Bool.true)
    addProof name type proof
    tokenChecks := tokenChecks.insert entry.constName! name
  let text := mkConst (data.str "text")
  let token := mkConst (data.str "token")
  let bank := mkConst (data.str "bank")
  let fuel := mkConst (data.str "fuel")
  let index := mkConst (data.str "rootIndex")
  let entries := mkConst (data.str "rootEntries")
  let stringsName ← localName base "strings_checked"
  let (stringsType, stringsValue) ← liftTermElabM <| libraryProof text stringChecks ``check_string ``chooseString
  addProof stringsName stringsType stringsValue
  let tokensName ← localName base "tokens_checked"
  let (tokensType, tokensValue) ← liftTermElabM <| libraryProof token tokenChecks ``check_number_token ``chooseNumber
  addProof tokensName tokensType tokensValue
  let selectedName ← localName base "root_selected"
  let selectedType ← liftTermElabM do
    mkEq (← mkAppM ``SourceBank.Bank.get #[bank, index]) (mkApp (mkConst ``SourceBank.Description.object) entries)
  let selectedValue ← liftTermElabM <| mkEqRefl (mkApp (mkConst ``SourceBank.Description.object) entries)
  addProof selectedName selectedType selectedValue
  let root := mkConst (data.str "root")
  let eagerType ← liftTermElabM do
    let bytes ← mkAppM ``SourceData.Node.bytes #[root]
    let value ← mkAppM ``SourceData.Node.value #[root]
    mkAppM ``EagerSource #[bytes, value]
  let eagerValue ← liftTermElabM <| mkAppM ``SourceBank.evaluate_object_eager
    #[text, token, bank, mkConst stringsName, mkConst tokensName, fuel, index, entries, mkConst selectedName]
  addProof (base.str "root_eager") eagerType eagerValue
  let parsed ← liftTermElabM <| mkAppM ``parse_of_eager #[mkConst (base.str "root_eager")]
  let type ← liftTermElabM <| inferType parsed
  addProof (base.str "parsed") type parsed
  logInfo m!"checked {strings.size} strings and {tokens.size} number tokens against the source bank"

private def sourceNat (value : Lean.Expr) : Option Nat :=
  if let some number := value.rawNatLit? then some number
  else if value.isAppOf ``OfNat.ofNat then value.getAppArgs[1]!.rawNatLit?
  else none

private partial def selectorBody (body : Lean.Expr) : CoreM Lean.Expr := do
  let body := body.consumeMData
  if body.isAppOf ``ite || (sourceNat body).isSome then return body
  let .defnInfo definition ← getConstInfo body.getAppFn.constName!
    | throwError "source selector must have a definition"
  selectorBody ((mkAppN definition.value body.getAppArgs).headBeta)

private partial def rleBranchProof (body : Lean.Expr) (proved : Std.HashMap Nat Name)
    (chooser : Name) : MetaM Lean.Expr := do
  let body ← selectorBody body
  if let some index := (sourceNat body) then
    let some proof := proved[index]? | throwError "unproved retained source address {index}"
    return mkConst proof
  let args := body.getAppArgs
  let left ← rleBranchProof args[3]! proved chooser
  let right ← rleBranchProof args[4]! proved chooser
  mkAppM chooser #[args[1]!, left, right]

private def rleSelectorProof (selector values : Lean.Expr) (common : Array Lean.Expr)
    (proved : Std.HashMap Nat Name) (property chooser : Name) : MetaM (Lean.Expr × Lean.Expr) :=
  withLocalDeclD `index (mkConst ``Nat) fun index => do
    let body ← selectorBody (mkApp selector index)
    let proof ← rleBranchProof body proved chooser
    let type := mkAppN (mkConst property) (common ++ #[mkApp selector index, mkApp values index])
    return (← mkForallFVars #[index] type, ← mkLambdaFVars #[index] proof)

private def sourcePair (entry : Lean.Expr) : MetaM (Lean.Expr × Lean.Expr) := do
  let entry ← whnf entry
  unless entry.isAppOf ``Prod.mk do throwError "expected source address and retained value"
  let args := entry.getAppArgs
  return (args[2]!, args[3]!)

private def selectionProof (base : Name) (label : String) (bank index : Lean.Expr) : CommandElabM Name := do
  let name ← localName base label
  let (type, value) ← liftTermElabM do
    let selected ← mkAppM ``SourceBank.Bank.get #[bank, index]
    let description ← withTransparency .all <| whnf selected
    return (← mkEq selected description, ← mkEqRefl description)
  addProof name type value
  return name

elab "certify_source_rle " base:ident " using " data:ident
    progress:(str)? : command => withEnableInfoTree false do
  let base := base.getId
  let data := data.getId
  let strings := mkConst (data.str "text")
  let tokens := mkConst (data.str "token")
  let bank := mkConst (data.str "bank")
  let fuel ← liftTermElabM do
    let value ← whnf (mkConst (data.str "fuel"))
    let some value := (sourceNat value) | throwError "source depth is not literal"
    unless value ≥ 3 do throwError "source depth is too small for retained columns"
    return value
  let blockCommon := #[strings, tokens, bank, mkNatLit (fuel - 3)]
  let columnCommon := #[strings, tokens, bank, mkNatLit (fuel - 1)]
  let naturalCommon := #[strings, tokens, bank, mkNatLit (fuel - 5)]
  let arrayCommon := #[strings, tokens, bank, mkNatLit (fuel - 4)]
  let naturalEntries ← liftTermElabM <| elements (mkConst (data.str "naturalSources"))
  let mut naturalChecks : Std.HashMap Nat Name := {}
  for entry in naturalEntries do
    let (index, value) ← liftTermElabM <| sourcePair entry
    let some address := sourceNat index | throwError "natural source address is not literal"
    let name ← localName base s!"rle_natural_{address}"
    let expected := mkApp (mkConst ``Lean.Json.num)
      (mkApp2 (mkConst ``Lean.JsonNumber.mk) (mkApp (mkConst ``Int.ofNat) value) (mkNatLit 0))
    let equality ← liftTermElabM <| mkEqRefl expected
    addProof name (mkAppN (mkConst ``SourceDecoding.NaturalAt) (naturalCommon ++ #[index, value]))
      (mkAppN (mkConst ``SourceDecoding.NaturalAt.mk) (naturalCommon ++ #[index, value, equality]))
    naturalChecks := naturalChecks.insert address name
  let arrays ← liftTermElabM <| elements (mkConst (data.str "valueArrays"))
  let mut arrayChecks : Std.HashMap Nat Name := {}
  for entry in arrays do
    let (binding, values) ← liftTermElabM <| sourcePair entry
    let fields ← liftCoreM do
      let .defnInfo definition ← getConstInfo binding.constName!
        | throwError "array binding must have a definition"
      return definition.value.getAppArgs
    unless fields.size == 4 do throwError "array binding must retain all four fields"
    let some address := sourceNat fields[0]! | throwError "array source address is not literal"
    if let some path := progress then
      IO.FS.writeFile path.getString s!"checking payload array {arrayChecks.size + 1}/{arrays.size}: {address}"
    let callbackName ← localName base s!"rle_array_elements_{address}"
    let (callbackType, callback) ← liftTermElabM <| rleSelectorProof fields[1]! fields[2]!
      naturalCommon naturalChecks ``SourceDecoding.NaturalAt ``SourceDecoding.NaturalAt.choose
    addProof callbackName callbackType callback
    let selected ← selectionProof base s!"rle_payload_selected_{address}" bank fields[0]!
    let proof ← liftTermElabM <| mkAppM ``SourceDecoding.naturals_at
      #[strings, tokens, bank, mkNatLit (fuel - 5), fields[0]!, fields[1]!, fields[2]!, fields[3]!,
        mkConst selected, mkConst callbackName]
    let name ← localName base s!"rle_payload_{address}"
    addProof name (mkAppN (mkConst ``SourceDecoding.NaturalsAt) (arrayCommon ++ #[fields[0]!, values])) proof
    arrayChecks := arrayChecks.insert address name
  let arrayEntries ← liftTermElabM <| elements (mkConst (data.str "blockArrays"))
  let mut blockArrays : Std.HashMap Nat Nat := {}
  for entry in arrayEntries do
    let (block, array) ← liftTermElabM <| sourcePair entry
    let some block := sourceNat block | throwError "block address is not literal"
    let some array := sourceNat array | throwError "payload address is not literal"
    blockArrays := blockArrays.insert block array
  let entries ← liftTermElabM <| elements (mkConst (data.str "blockSources"))
  let mut blockChecks : Std.HashMap Nat Name := {}
  for entry in entries do
    let (index, block) ← liftTermElabM <| sourcePair entry
    let some address := (sourceNat index) | throwError "source block address is not literal"
    if let some path := progress then
      IO.FS.writeFile path.getString s!"checking block {blockChecks.size + 1}/{entries.size}: {address}"
    let name ← localName base s!"rle_block_{address}"
    let type := mkAppN (mkConst ``SourceDecoding.BlockAt) (blockCommon ++ #[index, block])
    let proof ← if let some array := blockArrays[address]? then do
      let some arrayProof := arrayChecks[array]? | throwError "unproved retained payload array"
      let sourceValue ← liftTermElabM <| mkAppM ``SourceData.Node.value
        #[mkAppN (mkConst ``SourceBank.evaluate) (blockCommon ++ #[index])]
      let arrayValue ← liftTermElabM <| mkAppM ``SourceData.Node.value
        #[mkAppN (mkConst ``SourceBank.evaluate) (arrayCommon ++ #[mkNatLit array])]
      let expected := mkApp2 (mkConst ``SourceData.blockArrayTemplate) block arrayValue
      let shapeName ← localName base s!"rle_block_header_{address}"
      let shapeType ← liftTermElabM <| mkEq sourceValue expected
      let shapeProof ← liftTermElabM <| mkEqRefl expected
      addProof shapeName shapeType shapeProof
      liftTermElabM <| mkAppM ``SourceDecoding.BlockAt.of_naturals
        #[strings, tokens, bank, mkNatLit (fuel - 3), mkNatLit (fuel - 4), index,
          mkNatLit array, block, mkConst arrayProof, mkConst shapeName]
    else do
      let equality ← liftTermElabM <| mkEqRefl (mkApp (mkConst ``SourceData.blockJson) block)
      pure <| mkAppN (mkConst ``SourceDecoding.BlockAt.mk) (blockCommon ++ #[index, block, equality])
    addProof name type proof
    blockChecks := blockChecks.insert address name
  if let some path := progress then
    IO.FS.writeFile path.getString s!"all {blockChecks.size} block values checked"
  let bindings ← liftTermElabM <| elements (mkConst (data.str "columnBindings"))
  let mut columnChecks : Std.HashMap Nat Name := {}
  for entry in bindings do
    let (binding, column) ← liftTermElabM <| sourcePair entry
    let fields ← liftCoreM do
      let .defnInfo definition ← getConstInfo binding.constName!
        | throwError "column binding must have a definition"
      return definition.value.getAppArgs
    unless fields.size == 6 do throwError "column binding must retain all six fields"
    let some address := (sourceNat fields[0]!) | throwError "source column address is not literal"
    if let some path := progress then
      IO.FS.writeFile path.getString s!"checking column selector {columnChecks.size + 1}/{bindings.size}: {address}"
    let callbackName ← localName base s!"rle_blocks_{address}"
    let (callbackType, callback) ← liftTermElabM <| rleSelectorProof fields[3]! fields[4]!
      blockCommon blockChecks ``SourceDecoding.BlockAt ``SourceDecoding.BlockAt.choose
    addProof callbackName callbackType callback
    let selectedColumn ← selectionProof base s!"rle_column_selected_{address}" bank fields[0]!
    let selectedArray ← selectionProof base s!"rle_array_selected_{address}" bank fields[2]!
    let selectedKey ← localName base s!"rle_key_{address}"
    let (keyType, keyValue) ← liftTermElabM do
      let key := mkApp strings fields[1]!
      let expected := mkStrLit "blocks"
      return (← mkEq key expected, ← mkEqRefl expected)
    addProof selectedKey keyType keyValue
    let proof ← liftTermElabM <| mkAppM ``SourceDecoding.column_of_blocks
      #[strings, tokens, bank, mkNatLit (fuel - 3), fields[0]!, fields[1]!, fields[2]!,
        fields[3]!, fields[4]!, fields[5]!, mkConst selectedColumn, mkConst selectedKey,
        mkConst selectedArray, mkConst callbackName]
    let name ← localName base s!"rle_column_{address}"
    addProof name (mkAppN (mkConst ``SourceDecoding.ColumnAt) (columnCommon ++ #[fields[0]!, column])) proof
    columnChecks := columnChecks.insert address name
  if let some path := progress then
    IO.FS.writeFile path.getString s!"all {columnChecks.size} columns checked"
  let arrayIndex := mkConst (data.str "columnsIndex")
  let children := mkConst (data.str "columnsChildren")
  let columns := mkConst (data.str "column")
  let entries := mkConst (data.str "columnsEntries")
  let callbackName ← localName base "rle_columns_checked"
  let (callbackType, callback) ← liftTermElabM <| rleSelectorProof children columns
    columnCommon columnChecks ``SourceDecoding.ColumnAt ``SourceDecoding.ColumnAt.choose
  addProof callbackName callbackType callback
  let selected ← selectionProof base "rle_columns_selected" bank arrayIndex
  let decoded ← liftTermElabM <| mkAppM ``SourceDecoding.columns_at
    #[strings, tokens, bank, mkNatLit (fuel - 1), arrayIndex, children, columns, entries,
      mkConst selected, mkConst callbackName]
  let root := mkConst (data.str "root")
  let rootValue ← liftTermElabM <| mkAppM ``SourceData.Node.value #[root]
  let sourceValue ← liftTermElabM do
    mkAppM ``SourceData.Node.value #[mkAppN (mkConst ``SourceBank.evaluate)
      #[strings, tokens, bank, mkNatLit fuel, arrayIndex]]
  let fieldName ← localName base "rle_columns_field"
  let fieldType ← liftTermElabM do
    mkEq (← mkAppM ``Lean.Json.getObjValD #[rootValue, mkStrLit "columns"]) sourceValue
  let fieldProof ← liftTermElabM <| mkEqRefl sourceValue
  addProof fieldName fieldType fieldProof
  let proof ← liftTermElabM <| mkAppM ``SourceDecoding.columns_field_of_value #[mkConst fieldName, decoded]
  let type ← liftTermElabM <| inferType proof
  addProof (base.str "columns_decoded") type proof
  let (type, proof) ← liftTermElabM do
    let actual ← mkAppM ``Lean.Json.getObjValAs? #[rootValue, mkConst ``Nat, mkStrLit "trace_len"]
    let expected := mkAppN (mkConst ``Except.ok [Level.zero, Level.zero])
      #[mkConst ``String, mkConst ``Nat, mkConst (data.str "traceLength")]
    let type ← mkEq actual expected
    return (← instantiateMVars type, ← instantiateMVars (← mkEqRefl expected))
  addProof (base.str "trace_len_decoded") type proof
  logInfo m!"checked {blockChecks.size} retained RLE blocks and {columnChecks.size} physical columns"

end Airbender.Setup.SourceBankCertificate
