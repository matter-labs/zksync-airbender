module
public import Human.Compiler.NativeFixedRows.Checks.Common
public meta import Human.Compiler.NativeFixedRows.Checks.Common
public import Human.Compiler.NativeSetups.MulDiv

@[expose] public section
namespace Airbender.Compiler.NativeFixedRows.Checks.MulDiv000
open Airbender Airbender.Compiler

/- Bind every native row in this bounded slice. The compiled comparison is trusted. -/
check_native_grid "artifacts/setup/mul-div.json" [0, 262144] ([0, 1, 2, 3, 4, 5, 6, 7, 8]) =>
  (fun index => NativeFixedRows.mulDiv ⟨index.val + 0, by have bound := index.isLt; omega⟩)

end Airbender.Compiler.NativeFixedRows.Checks.MulDiv000
