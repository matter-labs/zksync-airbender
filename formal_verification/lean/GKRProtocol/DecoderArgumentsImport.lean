import GKRProtocol.DecoderArguments
import GKRProtocol.CleanLookupArgumentsImport

namespace Airbender.Compiler.DecoderArgumentsImport
open Lean Elab Command
set_option warningAsError true

private def fieldName (owner : Ident) (stem : String) : Ident :=
  mkIdent (owner.getId ++ Name.mkSimple stem)

private def emitChecked (command : Syntax) : CommandElabM Unit := do
  elabCommand command
  if (← get).messages.hasErrors then throwAbortCommand

syntax (name := importDecoderArguments) "import_decoder_arguments " ident " from " str " certificate " str
  " clean_model " ident " base_model " ident " lookup_model " ident " query_model " ident
  " links_model " ident " source_query " ident " trace_columns " ident " decoder_columns " ident : command

elab_rules : command
  | `(import_decoder_arguments $name:ident from $path:str certificate $certPath:str
      clean_model $cleanName:ident base_model $baseName:ident lookup_model $lookupName:ident
      query_model $queryName:ident links_model $linksName:ident source_query $sourceQuery:ident
      trace_columns $traceName:ident decoder_columns $decoderName:ident) => do
    let pair ← match Json.parse (← IO.FS.readFile path.getString) >>= (fromJson? (α := Import.Pair)) with
      | .ok pair => pure pair | .error error => throwError "{error}"
    let cert ← match Json.parse (← IO.FS.readFile certPath.getString) >>= (fromJson? (α := LookupImport.LookupCertificate)) with
      | .ok cert => pure cert | .error error => throwError "{error}"
    let [(description, rowIndex)] := cert.rows.toList.zipIdx.filter (fun (row, _) => row.kind == "decoder")
      | throwError "expected exactly one source decoder request"
    let decoder ← match pair.circuit.decoderColumns with
      | .ok decoder => pure decoder | .error error => throwError "{error}"
    if decoder.flags.isEmpty then throwError "decoder argument profile requires a retained selector mask"
    let logicalFields := #[0, 1, 2, 3, 4, 5, 6] ++ (if decoder.funct3.isSome then #[7] else #[]) ++ #[8]
    let payloadWidth := description.fields.size - 1
    unless description.fields.size > 0 &&
        (payloadWidth == logicalFields.size || payloadWidth == logicalFields.size + 1) do
      throwError "unsupported decoder padding/selector profile"
    let tagged := payloadWidth == logicalFields.size + 1
    let place := fieldName cleanName "placement"
    let environment := fieldName cleanName "environment"
    let fullBank := fieldName baseName "bank"
    let artifact := fieldName baseName "artifact"
    let nativeBank := fieldName queryName "bank"
    let sourcePlacement := fieldName lookupName "sourcePlacement"
    let copies := fieldName linksName "lookupCopies"
    let mut expressions : Array (TSyntax `term) := #[← `(_root_.Expression.var ⟨($traceName).execute⟩)]
    for index in logicalFields do
      expressions := expressions.push (← `((decoderExpressions $traceName $decoderName)[$(quote index)]))
    if tagged then expressions := expressions.push (← `(_root_.Expression.const (46 : Source.BaseField)))
    unless expressions.size == description.fields.size do throwError "decoder argument inventory changed"
    for h : index in [:expressions.size] do
      let expression := fieldName name s!"expression{index}"
      let nativeField := fieldName lookupName s!"field{rowIndex}_{index}"
      let nativeChecked := fieldName lookupName s!"fieldChecked{rowIndex}_{index}"
      let checked := fieldName name s!"checked{index}"
      let preserved := fieldName name s!"field_value{index}"
      emitChecked (← `(noncomputable def $expression : _root_.Expression Source.BaseField := $(expressions[index])))
      emitChecked (← `(theorem $checked : CleanExpression.nativeCheck $expression $place $fullBank
        ($nativeField).lowered $nativeBank = true := by decide +kernel))
      emitChecked (← `(theorem $preserved (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
        (arithmetic : ∀ gate ∈ ($artifact).gates, gate.expressionResidual (physical ∘ ($fullBank).address) = 0) :
        ($expression).eval ($environment physical data) =
          ($nativeField).source.value ((physical ∘ ($nativeBank).address) ∘ $sourcePlacement) :=
        (CleanExpression.native_value $expression $place $fullBank ($nativeField).lowered $nativeBank $checked physical data).trans
          (LookupFieldAgreement.sound $sourcePlacement $nativeChecked ($copies physical arithmetic)).symm))


    let payload := fieldName name "payloadExpressions"
    let queryFields := fieldName name "queryFields"
    let queryMask := fieldName name "queryMask"
    let payloadFields := fieldName name "payload_fields"
    let executeWeight := fieldName name "execute_weight"
    let queryValue := fieldName name "query_value"
    let executeExpression := fieldName name "expression0"
    let executeField := fieldName lookupName s!"field{rowIndex}_0"
    let executeValue := fieldName name "field_value0"
    let mut payloadTerms : Array (TSyntax `term) := #[]
    let mut sourceTerms : Array (TSyntax `term) := #[]
    let mut fieldProofs : Array Ident := #[]
    for index in [1:expressions.size] do
      let expression := fieldName name s!"expression{index}"
      let sourceField := fieldName lookupName s!"field{rowIndex}_{index}"
      payloadTerms := payloadTerms.push (← `($expression))
      sourceTerms := sourceTerms.push (← `(($sourceField).source))
      fieldProofs := fieldProofs.push (fieldName name s!"field_value{index}")
    emitChecked (← `(noncomputable def $payload : List (_root_.Expression Source.BaseField) := [$payloadTerms,*]))
    emitChecked (← `(theorem $queryFields : ($sourceQuery).fields = [$sourceTerms,*] := by rfl))
    emitChecked (← `(theorem $queryMask : ($sourceQuery).mask = some ($executeField).source := by rfl))
    let mut payloadProof ← `(rfl)
    for preserved in fieldProofs.reverse do
      payloadProof ← `(congrArg₂ List.cons ($preserved physical data arithmetic) $payloadProof)
    emitChecked (← `(theorem $payloadFields (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
      (arithmetic : ∀ gate ∈ ($artifact).gates, gate.expressionResidual (physical ∘ ($fullBank).address) = 0) :
      ($payload).map (fun expression => expression.eval ($environment physical data)) =
        ($sourceQuery).fields.map (fun field => field.value ((physical ∘ ($nativeBank).address) ∘ $sourcePlacement)) := by
      rw [$queryFields:ident]
      exact $payloadProof))
    emitChecked (← `(theorem $executeWeight (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
      (arithmetic : ∀ gate ∈ ($artifact).gates, gate.expressionResidual (physical ∘ ($fullBank).address) = 0) :
      ($sourceQuery).weight (RingHom.id _) ((physical ∘ ($nativeBank).address) ∘ $sourcePlacement) =
        ($executeExpression).eval ($environment physical data) := by
      simp only [SourceLookupQuery.weight, $queryMask:ident, RingHom.id_apply]
      exact ($executeValue physical data arithmetic).symm))
    emitChecked (← `(theorem $queryValue {R : Type} [CommRing R] (hom : Source.BaseField →+* R) (alpha gamma : R)
      (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
      (arithmetic : ∀ gate ∈ ($artifact).gates, gate.expressionResidual (physical ∘ ($fullBank).address) = 0) :
      ($sourceQuery).value hom alpha gamma ((physical ∘ ($nativeBank).address) ∘ $sourcePlacement) =
        RationalPair.leaf (hom (($executeExpression).eval ($environment physical data)))
          (NativeLookupEncoding.linearize hom alpha (($payload).map (fun expression => expression.eval ($environment physical data))) 0 0 + gamma) := by
      rw [SourceLookupQuery.value, source_query_weight_hom, $executeWeight:ident physical data arithmetic,
        ← $payloadFields:ident physical data arithmetic]))

end Airbender.Compiler.DecoderArgumentsImport
