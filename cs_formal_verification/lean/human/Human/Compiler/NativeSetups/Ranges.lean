module
public import Human.Helpers.Tables.Range
public import Human.Helpers.Context.Timestamps
public import Human.Compiler.NativeSetups.AddSub
public import Human.Compiler.NativeSetups.MulDiv
public import Human.Import.NativeGrid

@[expose] public section
namespace Airbender.Compiler.NativeSetups

/- Each setup import checks both complete virtual range columns. The check below
   also binds the generic 13-bit range model to every row of native table 26.
   This leaf keeps setup-file changes out of the ordinary range-proof dependency tree. -/

check_native_grid "artifacts/setup/mul-div.json" [196608, 8192] ([0]) => (fun index => #v[index.val])

end Airbender.Compiler.NativeSetups
