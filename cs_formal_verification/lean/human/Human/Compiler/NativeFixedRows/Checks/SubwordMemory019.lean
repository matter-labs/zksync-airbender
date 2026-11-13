module
public import Human.Compiler.NativeFixedRows.Checks.Common
public meta import Human.Compiler.NativeFixedRows.Checks.Common
public import Human.Compiler.NativeSetups.SubwordMemory

@[expose] public section
namespace Airbender.Compiler.NativeFixedRows.Checks.SubwordMemory019
open Airbender Airbender.Compiler

/- Bind every native row in this bounded slice. The compiled comparison is trusted. -/
check_native_grid "artifacts/setup/subword-memory.json" [4980736, 262144] ([0, 1, 2, 3, 4, 5, 6, 7, 8]) =>
  (fun index => Verification.subwordRow NativeFixedRows.Checks.words ⟨index.val + 4980736, by have bound := index.isLt; omega⟩)

end Airbender.Compiler.NativeFixedRows.Checks.SubwordMemory019
