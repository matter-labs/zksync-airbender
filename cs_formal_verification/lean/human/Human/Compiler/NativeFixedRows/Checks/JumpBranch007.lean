module
public import Human.Compiler.NativeFixedRows.Checks.Common
public meta import Human.Compiler.NativeFixedRows.Checks.Common
public import Human.Compiler.NativeSetups.JumpBranch

@[expose] public section
namespace Airbender.Compiler.NativeFixedRows.Checks.JumpBranch007
open Airbender Airbender.Compiler

/- Bind every native row in this bounded slice. The compiled comparison is trusted. -/
check_native_grid "artifacts/setup/jump-branch.json" [1835008, 262144] ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9]) =>
  (fun index => NativeFixedRows.jumpBranch ⟨index.val + 1835008, by have bound := index.isLt; omega⟩)

end Airbender.Compiler.NativeFixedRows.Checks.JumpBranch007
