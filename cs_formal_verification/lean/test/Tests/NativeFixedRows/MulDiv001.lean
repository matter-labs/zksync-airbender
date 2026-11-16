module
public import Tests.NativeFixedRows.Common
public meta import Tests.NativeFixedRows.Common
public import Human.Compiler.NativeSetups.MulDiv

@[expose] public section
namespace Tests.NativeFixedRows.MulDiv001
open Airbender Airbender.Compiler

/- Compare every native row in this slice with the mathematical fixed region. -/
check_native_grid "artifacts/setup/mul-div.json" [262144, 8192] ([0, 1, 2, 3, 4, 5, 6, 7, 8]) =>
  (fun index => Airbender.Compiler.NativeFixedRows.mulDiv ⟨index.val + 262144, by have bound := index.isLt; omega⟩)

end Tests.NativeFixedRows.MulDiv001
