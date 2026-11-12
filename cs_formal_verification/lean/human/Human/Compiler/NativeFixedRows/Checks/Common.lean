module
public import Human.Compiler.NativeFixedRows
public meta import Human.Compiler.NativeFixedRows
public meta import Human.Circuits.UnifiedReduced.Tables.SetupRV
public meta import Human.Circuits.UnifiedReduced.Tables.Setup
public meta import Human.Helpers.Tables.Bytes
public meta import Human.Helpers.Tables.Subword
public meta import Human.Helpers.Core.Word
public import Human.Import.NativeGrid

@[expose] public section
namespace Airbender.Compiler.NativeFixedRows.Checks

/-- The public image used by the pinned native setup fixture. -/
def words (index : Nat) : BitVec 32 :=
  match index with
  | 0 => 0x13
  | 1 => 0x00408093
  | 2 => 0x6f
  | 3 => 0x007181b3
  | _ => 0

end Airbender.Compiler.NativeFixedRows.Checks
