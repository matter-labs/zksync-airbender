module
public import Human.Import.SetupBlocks
public import Human.Compiler.NativeArithmetic

@[expose] public section
namespace Airbender.Compiler.NativeSetups
open Import.Setup NativeArithmetic

/-- Row `index` of lookup group `group` of an imported native setup, as field elements: the generic columns in
    native column order (group 0), the 16-bit range column (group 1) or the timestamp range column (group 2). -/
def importedRows (data : SetupData) (group : Fin 3) (index : Nat) : List F :=
  (if group.val = 0 then data.columns.toList.map (decode · index)
   else if group.val = 1 then [decode data.range16 index]
   else [decode data.timestampRange index]).map (fun value : Int => (value : F))

end Airbender.Compiler.NativeSetups
