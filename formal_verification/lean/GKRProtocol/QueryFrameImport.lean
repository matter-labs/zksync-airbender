import GKRProtocol.QueryFrame
import GKRProtocol.LookupImport

namespace Airbender.Compiler.QueryFrameImport
open Lean Elab Command
set_option warningAsError true

private def fieldName (owner : Ident) (stem : String) : Ident := mkIdent (owner.getId ++ Name.mkSimple stem)
private def checksSyntax (proofs : Array (TSyntax `term)) : CommandElabM (TSyntax `term) := do
  let mut result ← `(BoolChecks.nil)
  for proof in proofs.reverse do result ← `(BoolChecks.cons $proof $result)
  return result
theorem all_flatten_true (blocks : List (List α)) (predicate : α → Bool)
    (checked : blocks.all (fun block => block.all predicate) = true) :
    blocks.flatten.all predicate = true := by
  apply List.all_eq_true.mpr
  intro item member
  obtain ⟨block, included, inside⟩ := List.mem_flatten.mp member
  exact List.all_eq_true.mp (List.all_eq_true.mp checked block included) item inside

private def emitChecked (command : Syntax) : CommandElabM Unit := do
  elabCommand command
  if (← get).messages.hasErrors then throwAbortCommand

syntax (name := importQueryFrame) "import_query_frame " ident " certificate " str
  " queries " term " base_model " ident " lookup_model " ident " query_model " ident " source_model " ident
  " history_model " ident " helper_model " ident " counter_model " ident " inputs " num
  " phase " num " start " num " stop " num : command

elab_rules : command
  | `(import_query_frame $name:ident certificate $path:str queries $queryTerm:term
      base_model $baseName:ident lookup_model $lookupName:ident query_model $queryName:ident source_model $sourceName:ident
      history_model $historyName:ident helper_model $helperName:ident counter_model $counterName:ident
      inputs $arityNumber:num phase $phaseNumber:num start $startNumber:num stop $stopNumber:num) => do
    let cert ← match Json.parse (← IO.FS.readFile path.getString) >>= (fromJson? (α := LookupImport.LookupCertificate)) with
      | .ok cert => pure cert | .error error => throwError "{error}"
    let size := cert.rows.foldl (fun count row => count + row.fields.size) 0
    let phaseIndex := phaseNumber.getNat
    let firstIndex := startNumber.getNat
    let finalIndex := stopNumber.getNat
    unless phaseIndex ≤ 3 && firstIndex ≤ finalIndex && finalIndex ≤ size do
      throwError "invalid query frame proof slice"
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
    if phaseIndex == 0 || phaseIndex == 3 then
      emitChecked (← `(noncomputable def $queryList : List SourceLookupQuery := $queryTerm))
      emitChecked (← `(noncomputable def $fields : List Source.EncodedField := ($queryList).flatMap SourceLookupQuery.usedFields))
      emitChecked (← `(def $coordinates : List (Fin $(quote arityNumber.getNat)) :=
        ($history ++ List.ofFn $borrows) ++ List.ofFn $counters))
    let predicate ← `(fun field : Source.EncodedField =>
      erasureUntouched $coordinates (field.polynomial $placement) &&
        field.transportCheck $placement $oldPlacement $bank $oldBank)
    let checked := fieldName name "checked"
    if phaseIndex == 1 || phaseIndex == 3 then
      let mut proofs := #[]
      for index in [firstIndex:finalIndex] do
        let itemChecked := fieldName name s!"checked{index}"
        emitChecked (← `(theorem $itemChecked : ($predicate) (($fields).get ⟨$(quote index), by decide⟩) = true := by decide +kernel))
        proofs := proofs.push (← `($itemChecked))
      if phaseIndex == 1 then
        let block := fieldName name s!"block{firstIndex}"
        let blockChecked := fieldName name s!"blockChecked{firstIndex}"
        emitChecked (← `(noncomputable def $block : List Source.EncodedField :=
          (($fields).drop $(quote firstIndex)).take $(quote (finalIndex - firstIndex))))
        emitChecked (← `(theorem $blockChecked : ($block).all $predicate = true :=
          BoolChecks.all_true (predicate := $predicate) (items := $block) $(← checksSyntax proofs)))
      else
        emitChecked (← `(theorem $checked : ($fields).all $predicate = true :=
          BoolChecks.all_true (predicate := $predicate) (items := $fields) $(← checksSyntax proofs)))
    if phaseIndex == 0 || phaseIndex == 1 then return
    if phaseIndex == 2 then
      let mut blocks : Array (TSyntax `term) := #[]
      let mut proofs : Array (TSyntax `term) := #[]
      for first in (List.range ((size + 63) / 64)).map (· * 64) do
        let block := fieldName name s!"block{first}"
        let blockChecked := fieldName name s!"blockChecked{first}"
        blocks := blocks.push (← `($block))
        proofs := proofs.push (← `($blockChecked))
      let flattened := fieldName name "blocksFlatten"
      emitChecked (← `(theorem $flattened : ([$blocks,*] : List (List Source.EncodedField)).flatten = $fields := by rfl))
      let blockPredicate ← `(fun block : List Source.EncodedField => block.all $predicate)
      emitChecked (← `(theorem $checked : ($fields).all $predicate = true := by
        rw [← $flattened:ident]
        exact all_flatten_true [$blocks,*] $predicate
          (BoolChecks.all_true (predicate := $blockPredicate) (items := [$blocks,*]) $(← checksSyntax proofs))))
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
