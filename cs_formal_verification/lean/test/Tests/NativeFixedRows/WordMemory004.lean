module
public import Tests.NativeFixedRows.Common
public meta import Tests.NativeFixedRows.Common
public import Human.Compiler.NativeSetups.WordMemory

@[expose] public section
namespace Tests.NativeFixedRows.WordMemory004
open Airbender Airbender.Compiler

/- Compare every native row in this slice with the mathematical fixed region. -/
check_native_grid "artifacts/setup/word-memory.json" [1048576, 1] ([0, 1, 2, 3, 4, 5, 6, 7, 8]) =>
  (fun index => Airbender.Compiler.NativeFixedRows.wordMemory words ⟨index.val + 1048576, by have bound := index.isLt; omega⟩)

end Tests.NativeFixedRows.WordMemory004
