module
public import Human.Import.Columns
public meta import Human.Import.Columns
public import Human.Import.Coefficients
public meta import Human.Import.Coefficients
public import Human.Import.Operations
public meta import Human.Import.Operations
public meta import Proven.Import.GKRProtocol.CleanLookupArgumentsImport
public import Proven.Import.GKRProtocol.CleanLookupArgumentsImport

public meta section
set_option warningAsError true

namespace Airbender.Compiler.CleanGenericArgumentsImport
open Lean Elab Command

private def fieldName (owner : Ident) (stem : String) : Ident := mkIdent (owner.getId ++ Name.mkSimple stem)
private def emitChecked (command : Syntax) : CommandElabM Unit := do
  elabCommand command
  if (← get).messages.hasErrors then throwAbortCommand
private def constantSyntax (value : Int) : CommandElabM (TSyntax `term) := do
  let literal ← if value ≥ 0 then `(Int.ofNat $(quote value.toNat)) else `(Int.negSucc $(quote (-value - 1).toNat))
  `(Airbender.Expression.const (Int.cast $literal : Source.BaseField))
private partial def expressionSyntax : Expr → CommandElabM (TSyntax `term)
  | .Constant value => constantSyntax (Artifact.signedCoefficient value)
  | .Var index => `(Airbender.Expression.var ⟨$(quote index)⟩)
  | .Sum expressions => do expressions.foldlM (fun previous expression => do
      `(Airbender.Expression.add $previous $(← expressionSyntax expression))) (← constantSyntax 0)
  | .Product expressions => do expressions.foldlM (fun previous expression => do
      `(Airbender.Expression.mul $previous $(← expressionSyntax expression))) (← constantSyntax 1)

syntax (name := importCleanGenericArguments) "import_clean_generic_arguments " ident " from " str " certificate " str
  " clean_model " ident " base_model " ident " lookup_model " ident " query_model " ident
  " links_model " ident " start " num " stop " num
  (" part_size " num)? (" phase " num)? (" using_checks " ident)? : command

elab_rules : command
  | `(import_clean_generic_arguments $name:ident from $path:str certificate $certPath:str clean_model $cleanName:ident
      base_model $baseName:ident lookup_model $lookupName:ident query_model $queryName:ident links_model $linksName:ident
      start $first:num stop $last:num $[part_size $partSize:num]?
      $[phase $phaseNumber:num]? $[using_checks $wholeChecks:ident]?) => do
    let phaseIndex := (phaseNumber.map TSyntax.getNat).getD 2
    unless phaseIndex ≤ 2 do throwError "invalid Clean generic argument phase"
    if phaseIndex == 1 && wholeChecks.isNone then throwError "the complete generic phase requires checker facts"
    if phaseIndex == 0 && wholeChecks.isSome then throwError "the generic input phase cannot accept checker facts"
    if let some size := partSize then
      if size.getNat == 0 then throwError "the generic argument part size must be positive"
    let pair ← match Lean.Json.parse (← IO.FS.readFile path.getString) >>= (fromJson? (α := Import.Pair)) with
      | .ok pair => pure pair | .error error => throwError "{error}"
    let certData ← match Lean.Json.parse (← IO.FS.readFile certPath.getString) >>= (fromJson? (α := LookupImport.LookupCertificate)) with
      | .ok data => pure data | .error error => throwError "{error}"
    let place := fieldName cleanName "placement"
    let environment := fieldName cleanName "environment"
    let fullBank := fieldName baseName "bank"
    let artifact := fieldName baseName "artifact"
    let nativeBank := fieldName queryName "bank"
    let sourcePlacement := fieldName lookupName "sourcePlacement"
    let copies := fieldName linksName "lookupCopies"
    for queryIndex in [first.getNat:last.getNat] do
      let owner := match partSize with
        | none => name
        | some size => fieldName name s!"part{queryIndex / size.getNat}"
      let some query := pair.circuit.generic_lookups[queryIndex]? | throwError "Clean generic query is missing"
      let selected := certData.rows.toList.zipIdx.filter (fun (item, _) => item.kind == "generic" && item.native_index == queryIndex)
      let [(description, rowIndex)] := selected | throwError "Clean generic source coverage changed"
      let index := description.source_index
      unless query.lookup_set_index == queryIndex && query.columns.size == description.fields.size do
        throwError "Clean generic query width/order changed"
      for column in [:query.columns.size] do
        let some relation := query.columns[column]? | throwError "Clean generic column is missing"
        let expression ← match pair.circuit.lookupExpression relation with
          | .ok value => pure value | .error error => throwError "{error}"
        let cleanExpression := fieldName owner s!"genericExpression{index}_{column}"
        let nativeField := fieldName lookupName s!"field{rowIndex}_{column}"
        let nativeChecked := fieldName lookupName s!"fieldChecked{rowIndex}_{column}"
        let checked := fieldName owner s!"genericChecked{index}_{column}"
        let preserved := fieldName owner s!"generic_value{index}_{column}"
        if phaseIndex != 1 then
          emitChecked (← `(noncomputable def $cleanExpression : Airbender.Expression Source.BaseField := $(← expressionSyntax expression)))
        if phaseIndex == 0 then continue
        let checkProof ← match wholeChecks with
          | some proofOwner => `($(fieldName proofOwner s!"genericChecked{index}_{column}"))
          | none => `(by decide +kernel)
        emitChecked (← `(theorem $checked : CleanExpression.nativeCheck $cleanExpression $place $fullBank
          ($nativeField).lowered $nativeBank = true := $checkProof))
        emitChecked (← `(theorem $preserved (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
          (arithmetic : ∀ gate ∈ ($artifact).gates, gate.expressionResidual (physical ∘ ($fullBank).address) = 0) :
          ($cleanExpression).eval ($environment physical data) =
            ($nativeField).source.value ((physical ∘ ($nativeBank).address) ∘ $sourcePlacement) :=
          (CleanExpression.native_value $cleanExpression $place $fullBank ($nativeField).lowered $nativeBank $checked physical data).trans
            (LookupFieldAgreement.sound $sourcePlacement $nativeChecked ($copies physical arithmetic)).symm))

end Airbender.Compiler.CleanGenericArgumentsImport
