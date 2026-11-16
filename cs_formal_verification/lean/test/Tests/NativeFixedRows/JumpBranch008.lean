module
public import Tests.NativeFixedRows.Common
public meta import Tests.NativeFixedRows.Common
public import Human.Compiler.NativeSetups.JumpBranch

@[expose] public section
namespace Tests.NativeFixedRows.JumpBranch008
open Airbender Airbender.Compiler

/- Compare every native row in this slice with the mathematical fixed region. -/
check_native_grid "artifacts/setup/jump-branch.json" [2097152, 262144] ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9]) =>
  (fun index => Airbender.Compiler.NativeFixedRows.jumpBranch ⟨index.val + 2097152, by have bound := index.isLt; omega⟩)

end Tests.NativeFixedRows.JumpBranch008
