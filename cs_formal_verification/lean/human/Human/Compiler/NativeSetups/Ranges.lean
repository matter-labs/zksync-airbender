module
public import Human.Helpers.Tables.Range
public import Human.Helpers.Context.Timestamps
public import Human.Compiler.NativeSetups.AddSub
public import Human.Compiler.NativeSetups.JumpBranch
public import Human.Compiler.NativeSetups.MulDiv
public import Human.Compiler.NativeSetups.ShiftBinop
public import Human.Compiler.NativeSetups.WordMemory
public import Human.Compiler.NativeSetups.SubwordMemory
public import Human.Compiler.NativeSetups.Unified

@[expose] public section
namespace Airbender.Compiler.NativeSetups
open Import.Setup

/- Import claims of the range tables of the CPU setups. -/

/-- The native `RangeCheck13` table (table 26 of the multiply/divide setup, from row 196608) holds the key `index` of
    `Verification.range13Table` in column 0, zeros, and the tag 26, for every `index < 8192`. -/
def Range13ImportClaim : Prop :=
  ∀ index < 8192, ∀ column : Fin 9, decode (mulDivSetup.columns.getD column.val []) (196608 + index) =
    if column.val = 0 then (index : Int) else if column.val = 8 then 26 else 0

/-- The seven CPU setups. -/
noncomputable def cpuSetups : List SetupData :=
  [addSubSetup, jumpBranchSetup, mulDivSetup, shiftBinopSetup, wordMemorySetup, subwordMemorySetup, unifiedSetup]

/-- The 16-bit range column and the timestamp range column of each CPU setup hold the row index on their first `2^16`
    and `2^19` rows and zero on every later row of the trace, as `NativePublicSetup.rows` states for lookup groups 1
    and 2. -/
def CPURangesImportClaim : Prop :=
  ∀ data ∈ cpuSetups, ∀ index < data.traceLen,
    decode data.range16 index = (if index < 65536 then (index : Int) else 0) ∧
    decode data.timestampRange index = (if index < 524288 then (index : Int) else 0)

end Airbender.Compiler.NativeSetups
