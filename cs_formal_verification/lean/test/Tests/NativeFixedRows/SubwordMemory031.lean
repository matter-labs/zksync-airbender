module
public import Tests.NativeFixedRows.Common
public meta import Tests.NativeFixedRows.Common
public import Human.Compiler.NativeSetups.SubwordMemory

@[expose] public section
namespace Tests.NativeFixedRows.SubwordMemory031
open Airbender Airbender.Compiler

/- Compare every native row in this slice with the mathematical fixed region. -/
check_native_grid "artifacts/setup/subword-memory.json" [8126464, 262144] ([0, 1, 2, 3, 4, 5, 6, 7, 8]) =>
  (fun index => Verification.subwordRow words ⟨index.val + 8126464, by have bound := index.isLt; omega⟩)

end Tests.NativeFixedRows.SubwordMemory031
