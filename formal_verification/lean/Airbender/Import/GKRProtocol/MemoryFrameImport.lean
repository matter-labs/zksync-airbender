import Airbender.Proofs.GKRProtocol.MemoryFrame
import Airbender.Import.GKRProtocol.MemoryImport
import Airbender.Import.GKRProtocol.QueryFrameImport

namespace Airbender.Compiler.MemoryFrameImport
open Lean Elab Command
set_option warningAsError true

private def fieldName (owner : Ident) (stem : String) : Ident := mkIdent (owner.getId ++ Name.mkSimple stem)
private def checksSyntax (proofs : Array (TSyntax `term)) : CommandElabM (TSyntax `term) := do
  let mut result ← `(BoolChecks.nil)
  for proof in proofs.reverse do result ← `(BoolChecks.cons $proof $result)
  return result
private def emitChecked (command : Syntax) : CommandElabM Unit := do
  elabCommand command
  if (← get).messages.hasErrors then throwAbortCommand

syntax (name := importMemoryFrame) "import_memory_frame " ident " from " str
  " base_model " ident " memory_model " ident " source_model " ident " history_model " ident
  " helper_model " ident " counter_model " ident " inputs " num
  " phase " num " start " num " stop " num : command

elab_rules : command
  | `(import_memory_frame $name:ident from $path:str base_model $baseName:ident memory_model $memoryName:ident
      source_model $sourceName:ident history_model $historyName:ident helper_model $helperName:ident
      counter_model $counterName:ident inputs $arityNumber:num phase $phaseNumber:num start $startNumber:num stop $stopNumber:num) => do
    let snapshot ← match Json.parse (← IO.FS.readFile path.getString) >>= (fromJson? (α := Source.Snapshot)) with
      | .ok snapshot => pure snapshot | .error error => throwError "{error}"
    let requests ← match Source.memoryRequests snapshot.semantic_inputs with
      | .ok requests => pure requests | .error error => throwError "{error}"
    let phaseIndex := phaseNumber.getNat
    let firstIndex := startNumber.getNat
    let finalIndex := stopNumber.getNat
    let ramCount := 7 * (requests.reads.size + requests.writes.size)
    unless phaseIndex ≤ 3 && firstIndex ≤ finalIndex && finalIndex ≤ ramCount do
      throwError "invalid memory frame proof slice"
    let inputBank := fieldName baseName "inputBank"
    let fullBank := fieldName baseName "bank"
    let placement := fieldName memoryName "sourcePlacement"
    let nativeBank := fieldName memoryName "bank"
    let memoryValues := fieldName memoryName "sourceValues"
    let sourceExecute := fieldName memoryName "sourceExecute"
    let readRows := fieldName memoryName "memoryReadRows"
    let writeRows := fieldName memoryName "memoryWriteRows"
    let initReads := fieldName memoryName "initializationReadRows"
    let initWrites := fieldName memoryName "initializationWriteRows"
    let borrows := fieldName sourceName "slots"
    let histories := fieldName historyName "historyCells"
    let counters := fieldName counterName "slots"
    let assigned := fieldName counterName "assigned"
    let counterFrame := fieldName counterName "assigned_frame"
    let canonical := fieldName helperName "canonical"
    let activeFrame := fieldName helperName "canonical_active_frame"
    let canonicalFrame := fieldName helperName "canonical_frame"
    let execute := fieldName helperName "execute"
    let helperPlacement := fieldName baseName "helperPlacement"
    let activeCoordinates := fieldName name "activeCoordinates"
    let allCoordinates := fieldName name "allCoordinates"
    let baseline := fieldName name "sourceMemoryValues"
    let finiteActive := fieldName name "finite_active_frame"
    let finiteAll := fieldName name "finite_frame"
    if phaseIndex == 0 || phaseIndex == 3 then
      emitChecked (← `(def $activeCoordinates : List (Fin $(quote arityNumber.getNat)) :=
        List.ofFn $borrows ++ List.ofFn $counters))
      emitChecked (← `(def $allCoordinates : List (Fin $(quote arityNumber.getNat)) := $histories ++ $activeCoordinates))
      emitChecked (← `(noncomputable def $baseline (sourceValue : Fin $(quote arityNumber.getNat) → Source.BaseField)
        (fallback : GKRAddress → Source.BaseField) : Source.MemoryValues :=
        $memoryValues (($inputBank).materialize sourceValue fallback)))
      emitChecked (← `(theorem $finiteActive (sourceValue : Fin $(quote arityNumber.getNat) → Source.BaseField)
        (counts : Fin _ → Source.BaseField)
        (active : ($execute).value (($helperPlacement).memory.project sourceValue) ≠ 0)
        (index : Fin $(quote arityNumber.getNat)) (outside : index ∉ $activeCoordinates) :
        $assigned ($canonical sourceValue) counts index = sourceValue index := by
        have borrowOutside : ∀ borrow, $borrows borrow ≠ index := by
          intro borrow same
          exact outside (List.mem_append_left _ (List.mem_ofFn.mpr ⟨borrow, same⟩))
        have counterOutside : ∀ counter, $counters counter ≠ index := by
          intro counter same
          exact outside (List.mem_append_right _ (List.mem_ofFn.mpr ⟨counter, same⟩))
        exact ($counterFrame ($canonical sourceValue) counts index counterOutside).trans
          ($activeFrame sourceValue active index borrowOutside)))
      emitChecked (← `(theorem $finiteAll (sourceValue : Fin $(quote arityNumber.getNat) → Source.BaseField)
        (counts : Fin _ → Source.BaseField)
        (index : Fin $(quote arityNumber.getNat)) (outside : index ∉ $allCoordinates) :
        $assigned ($canonical sourceValue) counts index = sourceValue index := by
        have historyOutside : index ∉ $histories := fun member => outside (List.mem_append_left _ member)
        have borrowOutside : ∀ borrow, $borrows borrow ≠ index := by
          intro borrow same
          exact outside (List.mem_append_right _ (List.mem_append_left _ (List.mem_ofFn.mpr ⟨borrow, same⟩)))
        have counterOutside : ∀ counter, $counters counter ≠ index := by
          intro counter same
          exact outside (List.mem_append_right _ (List.mem_append_right _ (List.mem_ofFn.mpr ⟨counter, same⟩)))
        exact ($counterFrame ($canonical sourceValue) counts index counterOutside).trans
          ($canonicalFrame sourceValue index historyOutside borrowOutside)))
    for (stem, terms, fieldCount, coordinates, finite, active) in
        [("ram", ← `(($readRows ++ $writeRows).flatMap Source.MemoryRow.fields),
            7 * (requests.reads.size + requests.writes.size), activeCoordinates, finiteActive, true),
         ("initialization", ← `(($initReads ++ $initWrites).flatMap Source.MemoryRow.fields),
            28 * snapshot.configuration.inline_init_teardown_pairs, allCoordinates, finiteAll, false),
         ("execute", ← `([$sourceExecute]), 1, allCoordinates, finiteAll, false)] do
      let fields := fieldName name s!"{stem}Fields"
      let checked := fieldName name s!"{stem}Checked"
      if phaseIndex == 0 || phaseIndex == 3 then
        emitChecked (← `(noncomputable def $fields : List Source.MemoryField := $terms))
      let predicate ← `(fun field : Source.MemoryField => field.baseFrameCheck $placement $nativeBank $coordinates $inputBank $fullBank)
      if phaseIndex == 1 || phaseIndex == 3 then
        if stem == "ram" || phaseIndex == 3 || firstIndex == 0 then
          let sliceStart := if stem == "ram" then firstIndex else 0
          let sliceStop := if stem == "ram" then finalIndex else fieldCount
          let mut proofs := #[]
          for index in [sliceStart:sliceStop] do
            let itemChecked := fieldName name s!"{stem}Checked{index}"
            emitChecked (← `(theorem $itemChecked : ($predicate) (($fields).get ⟨$(quote index), by decide⟩) = true := by decide +kernel))
            proofs := proofs.push (← `($itemChecked))
          if phaseIndex == 1 && stem == "ram" then
            let block := fieldName name s!"ramBlock{firstIndex}"
            let blockChecked := fieldName name s!"ramBlockChecked{firstIndex}"
            emitChecked (← `(noncomputable def $block : List Source.MemoryField :=
              (($fields).drop $(quote sliceStart)).take $(quote (sliceStop - sliceStart))))
            emitChecked (← `(theorem $blockChecked : ($block).all $predicate = true :=
              BoolChecks.all_true (predicate := $predicate) (items := $block) $(← checksSyntax proofs)))
          else
            emitChecked (← `(theorem $checked : ($fields).all $predicate = true :=
              BoolChecks.all_true (predicate := $predicate) (items := $fields) $(← checksSyntax proofs)))
      if phaseIndex == 0 || phaseIndex == 1 then continue
      if phaseIndex == 2 && stem == "ram" then
        let mut blocks : Array (TSyntax `term) := #[]
        let mut proofs : Array (TSyntax `term) := #[]
        for first in (List.range ((ramCount + 63) / 64)).map (· * 64) do
          let block := fieldName name s!"ramBlock{first}"
          let blockChecked := fieldName name s!"ramBlockChecked{first}"
          blocks := blocks.push (← `($block))
          proofs := proofs.push (← `($blockChecked))
        let flattened := fieldName name "ramBlocksFlatten"
        emitChecked (← `(theorem $flattened : ([$blocks,*] : List (List Source.MemoryField)).flatten = $fields := by rfl))
        let blockPredicate ← `(fun block : List Source.MemoryField => block.all $predicate)
        emitChecked (← `(theorem $checked : ($fields).all $predicate = true := by
          rw [← $flattened:ident]
          exact QueryFrameImport.all_flatten_true [$blocks,*] $predicate
            (BoolChecks.all_true (predicate := $blockPredicate) (items := [$blocks,*]) $(← checksSyntax proofs))))
      let preserved := fieldName name s!"{stem}_fields_preserved"
      let activeBinder : Array (TSyntax `Lean.Parser.Term.bracketedBinder) ← if active then
          pure #[← `(bracketedBinder| (active : ($execute).value (($helperPlacement).memory.project sourceValue) ≠ 0))]
        else pure #[]
      let finiteProof ← if active then `($finite sourceValue counts active) else `($finite sourceValue counts)
      emitChecked (← `(theorem $preserved {width : Nat} (model : MaterializedLookupSetup width)
        (row : Fin model.imported.data.length)
        (sourceValue : Fin $(quote arityNumber.getNat) → Source.BaseField) (counts : Fin _ → Source.BaseField)
        (fallback : GKRAddress → Source.BaseField) (base : GKRAddress → Source.BaseField)
        (inputAgreement : ∀ index, base (($inputBank).address index) = $assigned ($canonical sourceValue) counts index)
        (externalAgreement : ∀ address,
          addressEqual (($fullBank).address (($fullBank).placement address)) address = false →
            base address = model.baseOracle row fallback address)
        $activeBinder:bracketedBinder* :
        ∀ field ∈ $fields, field.value ($memoryValues base) = field.value ($baseline sourceValue fallback) := by
        intro field member
        exact Source.MemoryField.base_frame_value field $placement $nativeBank $coordinates $inputBank $fullBank
          (List.all_eq_true.mp $checked field member) model row fallback sourceValue
          ($assigned ($canonical sourceValue) counts) base inputAgreement externalAgreement $finiteProof))

end Airbender.Compiler.MemoryFrameImport
