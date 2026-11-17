module
import Human.Compiler.NativeSetups.Bigint
import Human.Compiler.NativeSetups.BlakeG
import Human.Compiler.NativeSetups.MulDiv
import Human.Compiler.NativeSetups.ShiftBinop

/-! Spot checks of the imported setup data. Each `example` reads one value of an imported setup and the kernel
    compares it with the value that a reader finds in the JSON file at the stated path. A wrong value fails the
    build. A row `n` of a column lies in the block whose first row is the sum of the lengths of the blocks before
    it; the comment names that block and the row offset in it. -/

namespace Tests.ImportSetupSpotChecks
open Airbender.Import.Setup Airbender.Compiler.NativeSetups

/- `artifacts/setup/shift-binop.json`, `columns[0].blocks[10]` (affine, first row 524545, `first` 2013265920,
   `step` 0): row 524545 is decoder slot 0, the sentinel row; the field element `-1` is stored as 2013265920. -/
example : decode (shiftBinopSetup.columns.getD 0 []) 524545 = 2013265920 := by decide +kernel

/- `artifacts/setup/shift-binop.json`, `columns[9].blocks[7]` (affine, first row 524545, `first` 46, `step` 0): the
   decoder tag column of the sentinel row. -/
example : decode (shiftBinopSetup.columns.getD 9 []) 524545 = 46 := by decide +kernel

/- `artifacts/setup/mul-div.json`, `range16.blocks[0]` (affine, `length` 65536, `first` 0, `step` 1): the last row of
   the 16-bit range table holds 65535. -/
example : decode mulDivSetup.range16 65535 = 65535 := by decide +kernel

/- `artifacts/setup/mul-div.json`, `range16.blocks[1]` (affine, `first` 0, `step` 0): the padding after it is 0. -/
example : decode mulDivSetup.range16 65536 = 0 := by decide +kernel

/- `artifacts/setup/bigint.json`: row 1325356 is key 300 of the tag-41 table (offset 1325056). `columns[0].blocks[5]`
   (affine, first row 1325056, `first` 0, `step` 1) gives 300; `columns[1].blocks[4]` (periodic, first row 1325057,
   `values` [1, 2, 3, ...]) gives 300 % 256 = 44; `columns[2].blocks[5]` (affine, `first` 41, `step` 0) gives 41. -/
example : decode (bigintSetup.columns.getD 0 []) 1325356 = 300 := by decide +kernel
example : decode (bigintSetup.columns.getD 1 []) 1325356 = 44 := by decide +kernel
example : decode (bigintSetup.columns.getD 2 []) 1325356 = 41 := by decide +kernel

/- `artifacts/setup/blake-g.json`: row 4660 = 0x1234 of the 8-bit XOR table (tag 4) holds the keys 0x12 = 18 and
   0x34 = 52 and their XOR 0x26 = 38. `columns[0].blocks[0]` (periodic, `repetitions` 256, `stride` 1) gives 18;
   `columns[1].blocks[0]` (periodic, `values` [0, 1, 2, ...]) gives 52; `columns[2].blocks[18]` (periodic, first row
   4608, `values` [18, 19, 16, 17, ...], `stride` 32) gives 38; `columns[8].blocks[0]` (affine, `first` 4) gives 4. -/
example : decode (blakeGSetup.columns.getD 0 []) 4660 = 18 := by decide +kernel
example : decode (blakeGSetup.columns.getD 1 []) 4660 = 52 := by decide +kernel
example : decode (blakeGSetup.columns.getD 2 []) 4660 = 38 := by decide +kernel
example : decode (blakeGSetup.columns.getD 8 []) 4660 = 4 := by decide +kernel

end Tests.ImportSetupSpotChecks
