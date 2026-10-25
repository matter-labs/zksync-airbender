import GKRProtocol.CleanArguments
import GKRProtocol.CleanArithmeticImport
import Airbender.Import.Parse
import GKRProtocol.LookupImport

namespace Airbender.Compiler.CleanLookupArgumentsImport
open Lean Elab Command
set_option warningAsError true

private def fieldName (owner : Ident) (stem : String) : Ident := mkIdent (owner.getId ++ Name.mkSimple stem)
private def emitChecked (command : Syntax) : CommandElabM Unit := do
  elabCommand command
  if (← get).messages.hasErrors then throwAbortCommand
private def constantSyntax (value : Int) : CommandElabM (TSyntax `term) := do
  let literal ← if value ≥ 0 then `(Int.ofNat $(quote value.toNat)) else `(Int.negSucc $(quote (-value - 1).toNat))
  `(_root_.Expression.const (Int.cast $literal : Source.BaseField))
private partial def expressionSyntax : Expr → CommandElabM (TSyntax `term)
  | .Constant value => constantSyntax (Artifact.signedCoefficient value)
  | .Var index => `(_root_.Expression.var ⟨$(quote index)⟩)
  | .Sum expressions => do expressions.foldlM (fun previous expression => do
      `(_root_.Expression.add $previous $(← expressionSyntax expression))) (← constantSyntax 0)
  | .Product expressions => do expressions.foldlM (fun previous expression => do
      `(_root_.Expression.mul $previous $(← expressionSyntax expression))) (← constantSyntax 1)

syntax (name := importCleanLookupArguments) "import_clean_lookup_arguments " ident " from " str " certificate " str
  " clean_model " ident " base_model " ident " lookup_model " ident " query_model " ident
  " links_model " ident : command

elab_rules : command
  | `(import_clean_lookup_arguments $name:ident from $path:str certificate $certPath:str clean_model $cleanName:ident
      base_model $baseName:ident lookup_model $lookupName:ident query_model $queryName:ident links_model $linksName:ident) => do
    let pair ← match Json.parse (← IO.FS.readFile path.getString) >>= (fromJson? (α := Import.Pair)) with
      | .ok pair => pure pair | .error error => throwError "{error}"
    let certData ← match Json.parse (← IO.FS.readFile certPath.getString) >>= (fromJson? (α := LookupImport.LookupCertificate)) with
      | .ok data => pure data | .error error => throwError "{error}"
    let expressions ← match pair.circuit.range16Expressions with
      | .ok data => pure data | .error error => throwError "{error}"
    let place := fieldName cleanName "placement"
    let environment := fieldName cleanName "environment"
    let fullBank := fieldName baseName "bank"
    let artifact := fieldName baseName "artifact"
    let nativeBank := fieldName queryName "bank"
    let sourcePlacement := fieldName lookupName "sourcePlacement"
    let copies := fieldName linksName "lookupCopies"
    let mut ranges : Array (Option (TSyntax `term)) := Array.replicate expressions.size none
    for (description, rowIndex) in certData.rows.toList.zipIdx do
      unless description.kind == "range16" do continue
      let some expression := expressions[description.native_index]? | throwError "Clean scalar query is missing"
      let index := description.source_index
      let cleanExpression := fieldName name s!"rangeExpression{index}"
      let nativeField := fieldName lookupName s!"field{rowIndex}_0"
      let nativeChecked := fieldName lookupName s!"fieldChecked{rowIndex}_0"
      let checked := fieldName name s!"rangeChecked{index}"
      let preserved := fieldName name s!"range_value{index}"
      emitChecked (← `(noncomputable def $cleanExpression : _root_.Expression Source.BaseField := $(← expressionSyntax expression)))
      emitChecked (← `(theorem $checked : CleanExpression.nativeCheck $cleanExpression $place $fullBank
        ($nativeField).lowered $nativeBank = true := by decide +kernel))
      emitChecked (← `(theorem $preserved (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
        (arithmetic : ∀ gate ∈ ($artifact).gates, gate.expressionResidual (base ∘ ($fullBank).address) = 0) :
        ($cleanExpression).eval ($environment base data) =
          ($nativeField).source.value ((base ∘ ($nativeBank).address) ∘ $sourcePlacement) :=
        (CleanExpression.native_value $cleanExpression $place $fullBank ($nativeField).lowered $nativeBank $checked base data).trans
          (LookupFieldAgreement.sound $sourcePlacement $nativeChecked ($copies base arithmetic)).symm))
      if (ranges[description.native_index]!).isSome then throwError "duplicate Clean range expression"
      ranges := ranges.set! description.native_index (some (← `($cleanExpression)))
    unless ranges.all Option.isSome do throwError "Clean scalar argument coverage changed"
    let rangeTerms ← ranges.mapM fun item => match item with
      | some item => pure item | none => throwError "missing Clean range expression"
    let rangeExpressions := fieldName name "rangeExpressions"
    emitChecked (← `(noncomputable def $rangeExpressions : List (_root_.Expression Source.BaseField) := [$rangeTerms,*]))

end Airbender.Compiler.CleanLookupArgumentsImport
