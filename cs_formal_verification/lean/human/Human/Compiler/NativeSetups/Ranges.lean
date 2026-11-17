module
public import Human.Helpers.Tables.Range
public import Human.Helpers.Context.Timestamps
public import Human.Compiler.NativeSetups.AddSub
public import Human.Compiler.NativeSetups.MulDiv

@[expose] public section
namespace Airbender.Compiler.NativeSetups
open Import.Setup

/-- The native `RangeCheck13` table (table 26 of the multiply/divide setup, from row 196608) holds the key `index` of
    `Verification.range13Table` in column 0, zeros, and the tag 26, for every `index < 8192`. -/
def Range13ImportClaim : Prop :=
  ∀ index < 8192, ∀ column : Fin 9, decode (mulDivSetup.columns.getD column.val []) (196608 + index) =
    if column.val = 0 then (index : Int) else if column.val = 8 then 26 else 0

end Airbender.Compiler.NativeSetups
