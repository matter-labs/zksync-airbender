module
public import Tests.NativeFixedRows.Common
public meta import Tests.NativeFixedRows.Common
public import Human.Compiler.NativeSetups.Unified

@[expose] public section
namespace Tests.NativeFixedRows.Unified007
open Airbender Airbender.Compiler

/- Compare every native row in this slice with the mathematical fixed region. -/
check_native_grid "artifacts/setup/unified.json" [1835008, 262144] ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9]) =>
  (fun index => Airbender.Compiler.NativeFixedRows.unified Airbender.Compiler.NativeSetups.fixtureWords ⟨index.val + 1835008, by have bound := index.isLt; omega⟩)

end Tests.NativeFixedRows.Unified007
