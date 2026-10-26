import Airbender.Proofs.GKRProtocol.CleanHelperArguments
import Airbender.Import.Parse
import Airbender.Import.GKRProtocol.FullArithmeticImport

namespace Airbender.Compiler.CleanHelperArgumentsImport
open Lean Elab Command
set_option warningAsError true
structure Operand where
  native_leaf : Nat
  source_index : Nat
  deriving FromJson
structure Indices where
  operands : Array Operand
  deriving FromJson
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

syntax (name := importCleanHelperArguments) "import_clean_helper_arguments " ident " from " str " helper_indices " str
  " clean_model " ident " base_model " ident " helper_model " ident " memory_model " ident " links_model " ident : command
elab_rules : command
  | `(import_clean_helper_arguments $name:ident from $path:str helper_indices $indexText:str
      clean_model $cleanName:ident base_model $baseName:ident helper_model $helperName:ident
      memory_model $memoryName:ident links_model $linksName:ident) => do
    let pair ← match Json.parse (← IO.FS.readFile path.getString) >>= (fromJson? (α := Import.Pair)) with
      | .ok pair => pure pair | .error error => throwError "{error}"
    let indices ← match Json.parse indexText.getString >>= (fromJson? (α := Indices)) with
      | .ok data => pure data | .error error => throwError "{error}"
    let expressions ← match pair.circuit.timestampExpressions with
      | .ok data => pure data | .error error => throwError "{error}"
    unless indices.operands.size == expressions.size do throwError "Clean helper operand coverage changed"
    let place := fieldName cleanName "placement"
    let environment := fieldName cleanName "environment"
    let fullBank := fieldName baseName "bank"
    let artifact := fieldName baseName "artifact"
    let nativeBank := fieldName memoryName "bank"
    let helperPlacement := fieldName helperName "placement"
    let helperValues := fieldName helperName "sourceValues"
    let helperFields := fieldName helperName "fields"
    let copies := fieldName linksName "helperCopies"
    let mut timestamps : Array (TSyntax `term) := #[]
    for index in [:expressions.size] do
      let selectedOps := indices.operands.filter (·.source_index == index)
      unless selectedOps.size == 1 do throwError "Clean helper source index is missing or duplicated"
      let some operand := selectedOps[0]? | throwError "missing helper operand"
      let some expression := expressions[index]? | throwError "Clean helper expression is missing"
      let cleanExpression := fieldName name s!"timestampExpression{index}"
      let recipe := fieldName helperName s!"recipe{operand.native_leaf}"
      let candidate := fieldName helperName s!"candidate{operand.native_leaf}"
      let helperChecked := fieldName helperName s!"checked{operand.native_leaf}"
      let inBank := fieldName helperName s!"inBank{operand.native_leaf}"
      let checked := fieldName name s!"timestampChecked{index}"
      let fieldMatch := fieldName name s!"timestampFieldMatch{index}"
      let preserved := fieldName name s!"timestamp_value{index}"
      let bounded := fieldName name s!"timestamp_bound{index}"
      emitChecked (← `(noncomputable def $cleanExpression : _root_.Expression Source.BaseField := $(← expressionSyntax expression)))
      emitChecked (← `(theorem $checked : CleanExpression.nativeCheck $cleanExpression $place $fullBank
        (($recipe).expression (($nativeBank).placement)) $nativeBank = true := by decide +kernel))
      emitChecked (← `(theorem $fieldMatch : ($candidate).source = ($helperFields).get ⟨$(quote index), by decide⟩ := by rfl))
      emitChecked (← `(theorem $preserved (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
        (arithmetic : ∀ gate ∈ ($artifact).gates, gate.expressionResidual (base ∘ ($fullBank).address) = 0) :
        ($cleanExpression).eval ($environment base data) = ($candidate).source.value ($helperValues base) :=
        (CleanExpression.helper_value $cleanExpression $place $fullBank $recipe $nativeBank $checked $inBank base data).trans
          (($candidate).sound $helperPlacement $nativeBank $helperChecked $inBank base ($copies base arithmetic)).symm))
      emitChecked (← `(theorem $bounded (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
        (arithmetic : ∀ gate ∈ ($artifact).gates, gate.expressionResidual (base ∘ ($fullBank).address) = 0)
        (helpers : ∀ field ∈ $helperFields, (field.value ($helperValues base)).val < 524288) :
        (($cleanExpression).eval ($environment base data)).val < 524288 := by
        rw [$preserved base data arithmetic, $fieldMatch:ident]
        exact helpers _ (List.get_mem $helperFields ⟨$(quote index), by decide⟩)))
      timestamps := timestamps.push (← `($cleanExpression))
    let timestampExpressions := fieldName name "timestampExpressions"
    emitChecked (← `(noncomputable def $timestampExpressions : List (_root_.Expression Source.BaseField) := [$timestamps,*]))

end Airbender.Compiler.CleanHelperArgumentsImport
