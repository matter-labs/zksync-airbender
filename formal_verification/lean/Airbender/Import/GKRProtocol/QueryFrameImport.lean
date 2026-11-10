import Airbender.Proofs.GKRProtocol.QueryFrame
import Airbender.Import.GKRProtocol.LookupImport

namespace Airbender.Compiler.QueryFrameImport
open Lean Elab Command
set_option warningAsError true

private def fieldName (owner : Ident) (stem : String) : Ident := mkIdent (owner.getId ++ Name.mkSimple stem)
private def emitChecked (command : Syntax) : CommandElabM Unit := do
  elabCommand command
  if (← get).messages.hasErrors then throwAbortCommand

syntax (name := importQueryFrame) "import_query_frame " ident " certificate " str
  " queries " term " base_model " ident " lookup_model " ident " query_model " ident " source_model " ident
  " history_model " ident " helper_model " ident " counter_model " ident " inputs " num
  " phase " num " start " num " stop " num (" using_check " term)? : command

elab_rules : command
  | `(import_query_frame $name:ident certificate $path:str queries $queryTerm:term
      base_model $baseName:ident lookup_model $lookupName:ident query_model $queryName:ident source_model $sourceName:ident
      history_model $historyName:ident helper_model $helperName:ident counter_model $counterName:ident
      inputs $arityNumber:num phase $phaseNumber:num start $startNumber:num stop $stopNumber:num
      $[using_check $wholeCheck:term]?) => do
    let cert ← match Json.parse (← IO.FS.readFile path.getString) >>= (fromJson? (α := LookupImport.LookupCertificate)) with
      | .ok cert => pure cert | .error error => throwError "{error}"
    let size := cert.rows.foldl (fun count row => count + row.fields.size) 0
    let phaseIndex := phaseNumber.getNat
    let firstIndex := startNumber.getNat
    let finalIndex := stopNumber.getNat
    unless (phaseIndex == 0 || phaseIndex == 3) && firstIndex ≤ finalIndex && finalIndex ≤ size do
      throwError "query frames require a data phase or a complete check"
    let placement := fieldName baseName "originalProjection"
    let bank := fieldName baseName "inputBank"
    let oldPlacement := fieldName lookupName "sourcePlacement"
    let oldBank := fieldName queryName "bank"
    let history := fieldName historyName "historyCells"
    let borrows := fieldName sourceName "slots"
    let counters := fieldName counterName "slots"
    let assigned := fieldName counterName "assigned"
    let counterFrame := fieldName counterName "assigned_frame"
    let canonical := fieldName helperName "canonical"
    let canonicalFrame := fieldName helperName "canonical_frame"
    let queryList := fieldName name "queries"
    let fields := fieldName name "fields"
    let coordinates := fieldName name "coordinates"
    if phaseIndex == 0 || (phaseIndex == 3 && wholeCheck.isNone) then
      emitChecked (← `(noncomputable def $queryList : List SourceLookupQuery := $queryTerm))
      emitChecked (← `(noncomputable def $fields : List Source.EncodedField := ($queryList).flatMap SourceLookupQuery.usedFields))
      emitChecked (← `(def $coordinates : List (Fin $(quote arityNumber.getNat)) :=
        ($history ++ List.ofFn $borrows) ++ List.ofFn $counters))
    let predicate ← `(fun field : Source.EncodedField =>
      erasureUntouched $coordinates (field.polynomial $placement) &&
        field.transportCheck $placement $oldPlacement $bank $oldBank)
    let length := fieldName name "fieldsLength"
    if phaseIndex == 0 then
      emitChecked (← `(theorem $length : ($fields).length = $(quote size) := by decide +kernel))
    let checked := fieldName name "checked"
    if phaseIndex == 0 then return
    let proof ← match wholeCheck with
      | some complete => pure complete
      | none => `(by decide +kernel)
    emitChecked (← `(theorem $checked : ($fields).all $predicate = true := $proof))
    let preserved := fieldName name "fields_preserved"
    emitChecked (← `(theorem $preserved
      (sourceValue : Fin $(quote arityNumber.getNat) → Source.BaseField) (counts : Fin _ → Source.BaseField)
      (base : GKRAddress → Source.BaseField)
      (inputAgreement : ∀ wire, base (($bank).address wire) = $assigned ($canonical sourceValue) counts wire) :
      ∀ field ∈ $fields, field.value ((base ∘ ($oldBank).address) ∘ $oldPlacement) =
        field.value (sourceValue ∘ $placement) := by
      intro field member
      have clauses : erasureUntouched $coordinates (field.polynomial $placement) = true ∧
          field.transportCheck $placement $oldPlacement $bank $oldBank = true := by
        simpa only [Bool.and_eq_true] using List.all_eq_true.mp $checked field member
      refine (Source.EncodedField.transport_value field $placement $oldPlacement $bank $oldBank
        clauses.2 _ base inputAgreement).trans ?_
      apply Source.EncodedField.frame_value field $placement $coordinates clauses.1
      intro index outside
      have historyOutside : index ∉ $history := fun member => outside (List.mem_append_left _ (List.mem_append_left _ member))
      have borrowOutside : ∀ borrow, $borrows borrow ≠ index := by
        intro borrow same
        exact outside (List.mem_append_left _ (List.mem_append_right _ (List.mem_ofFn.mpr ⟨borrow, same⟩)))
      have counterOutside : ∀ counter, $counters counter ≠ index := by
        intro counter same
        exact outside (List.mem_append_right _ (List.mem_ofFn.mpr ⟨counter, same⟩))
      exact ($counterFrame ($canonical sourceValue) counts index counterOutside).trans
        ($canonicalFrame sourceValue index historyOutside borrowOutside)))
    let preservedQueries := fieldName name "queries_preserved"
    emitChecked (← `(theorem $preservedQueries {R : Type} [CommRing R]
      (hom : Source.BaseField →+* R) (alpha gamma : R)
      (sourceValue : Fin $(quote arityNumber.getNat) → Source.BaseField) (counts : Fin _ → Source.BaseField)
      (base : GKRAddress → Source.BaseField)
      (inputAgreement : ∀ wire, base (($bank).address wire) = $assigned ($canonical sourceValue) counts wire) :
      ∀ query ∈ $queryList, query.value hom alpha gamma ((base ∘ ($oldBank).address) ∘ $oldPlacement) =
        query.value hom alpha gamma (sourceValue ∘ $placement) := by
      intro query member
      apply SourceLookupQuery.value_congr
      intro field included
      exact $preserved sourceValue counts base inputAgreement field (List.mem_flatMap.mpr ⟨query, member, included⟩)))

end Airbender.Compiler.QueryFrameImport
