import Airbender.Import.Blake2Worker

namespace Airbender.Import.Blake2Processing
open Lean Elab Command

/-- Column walk from the selected native quotient's processing-conventions
    function. This imports descriptors; the source polynomial rule is reviewed
    separately. It does not import physical verifier acceptance. -/
def maskedColumns (abi : Airbender.Blake2Worker.ABI) : Array Nat :=
  #[abi.offsetHigh] ++ abi.writeTime.toArray ++ abi.registers.flatMap fun register =>
    (#[register.access] ++ register.indirects).flatMap fun access =>
      access.readTime.toArray ++ access.readValue.toArray ++
        access.writeValue.elim #[] Vector.toArray

elab "import_native_blake2_processing " name:ident " from " path:str : command => do
  let source ← IO.FS.readFile path.getString
  let c ← match Airbender.Import.Blake2Worker.parse source with
    | .ok c => pure c | .error e => throwError "Blake2 processing import failed: {e}"
  let masked := maskedColumns c.abi
  let memory ← match (Array.range c.abi.memoryWidth).mapM (fun i => c.logical (.MemorySubtree i)) with
    | .ok columns => pure columns | .error e => throwError e
  let multiplicity := mkIdent (name.getId.appendAfter "Multiplicity")
  let columns := mkIdent (name.getId.appendAfter "MaskedColumns")
  let memoryColumns := mkIdent (name.getId.appendAfter "MemoryColumns")
  let bytes := mkIdent (name.getId.appendAfter "SourceBytes")
  elabCommand (← `(def $multiplicity : Nat := $(quote c.abi.multiplicity)))
  elabCommand (← `(def $columns : Array Nat := $(quote masked)))
  elabCommand (← `(def $memoryColumns : Array Nat := $(quote memory)))
  elabCommand (← `(def $bytes : String := $(quote source)))

end Airbender.Import.Blake2Processing
