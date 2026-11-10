import Airbender.Import.GKRProtocol.MemoryFrameImport
import Airbender.Import.GKRProtocol.HelperImport

namespace Airbender.Compiler.MemoryExecuteImport
open Lean Elab Command
set_option warningAsError true

private def fieldName (owner : Ident) (stem : String) : Ident := mkIdent (owner.getId ++ Name.mkSimple stem)
private def emitChecked (command : Syntax) : CommandElabM Unit := do
  elabCommand command
  if (← get).messages.hasErrors then throwAbortCommand

syntax (name := importMemoryExecute) "import_memory_execute " ident
  " base_model " ident " memory_model " ident " helper_model " ident
  " helper_fields " ident " frame_model " ident " inputs " num : command

elab_rules : command
  | `(import_memory_execute $name:ident base_model $baseName:ident memory_model $memoryName:ident
      helper_model $helperName:ident helper_fields $fieldsName:ident frame_model $frameName:ident inputs $arityNumber:num) => do
    let fullAddresses := fieldName baseName "addresses"
    let fullUnique := fieldName baseName "addressesUnique"
    let initialSegment := fieldName baseName "inputPrefix"
    let inputAddresses := fieldName baseName "inputs"
    let inputBank := fieldName baseName "inputBank"
    let fullPlacement := fieldName baseName "helperPlacement"
    let nativePlacement := fieldName fieldsName "placement"
    let nativeBank := fieldName memoryName "bank"
    let memoryExecute := fieldName memoryName "sourceExecute"
    let helperExecute := fieldName helperName "execute"
    let baseline := fieldName frameName "sourceMemoryValues"
    let inputUnique := fieldName name "inputsUnique"
    let inputRoundTrip := fieldName name "inputRoundTrip"
    let sameExecute := fieldName name "executeFieldMatch"
    let transport := fieldName name "executeTransportChecked"
    emitChecked (← `(theorem $inputUnique : ($inputAddresses).Nodup := by
      have unique : (($fullAddresses).take $(quote arityNumber.getNat)).Nodup := ($fullUnique).take
      simpa only [$initialSegment:ident] using unique))
    emitChecked (← `(theorem $inputRoundTrip (index : Fin $(quote arityNumber.getNat)) :
      ($inputBank).placement (($inputBank).address index) = index :=
      WireBank.ofList_roundTrip $inputAddresses (by decide) $inputUnique index))
    emitChecked (← `(theorem $sameExecute : $memoryExecute = $helperExecute := by rfl))
    emitChecked (← `(theorem $transport :
      (Source.HelperField.memory $memoryExecute).transportCheck $fullPlacement $nativePlacement $inputBank $nativeBank = true := by decide +kernel))
    let agrees := fieldName name "execute_source"
    emitChecked (← `(theorem $agrees (sourceValue : Fin $(quote arityNumber.getNat) → Source.BaseField)
      (fallback : GKRAddress → Source.BaseField) :
      ($memoryExecute).value ($baseline sourceValue fallback) =
        ($helperExecute).value (($fullPlacement).memory.project sourceValue) := by
      have interpretation := Source.HelperField.transport_value (Source.HelperField.memory $memoryExecute)
        $fullPlacement $nativePlacement $inputBank $nativeBank $transport sourceValue
        (($inputBank).materialize sourceValue fallback)
        (fun index => WireBank.materialize_at $inputBank $inputRoundTrip sourceValue fallback index)
      exact interpretation))

end Airbender.Compiler.MemoryExecuteImport
