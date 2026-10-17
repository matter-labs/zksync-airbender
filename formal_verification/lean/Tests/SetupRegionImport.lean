import Airbender.Import.SetupRegionEmbed

namespace Tests.SetupRegionImport
open Airbender.Setup
set_option warningAsError true
set_option Elab.async false

private def source : Column := ⟨#[.affine 4 0 1,
  .periodic 2 8 #[4, 5, 6, 7], .dense #[20, 21]]⟩
private def selected : Column := ⟨#[.affine 2 2 1,
  .periodic 2 8 #[4, 5, 6, 7]]⟩

/-- A slice can start inside a block and cross a periodic block boundary. -/
theorem crosses_blocks : Slices.matchesSource source selected 2 10 = true := by decide +kernel

/-- A slice can start in the second repetition and end in a dense block. -/
theorem partial_period :
    Slices.matchesSource source ⟨#[.dense #[13, 14, 15, 20]]⟩ 9 4 = true := by decide +kernel

theorem wrong_offset : Slices.matchesSource source selected 1 10 = false := by decide +kernel

theorem wrong_value :
    Slices.matchesSource source ⟨#[.affine 2 2 1,
      .periodic 2 8 #[4, 5, 6, 8]]⟩ 2 10 = false := by decide +kernel

theorem missing_rows :
    Slices.matchesSource source ⟨#[.affine 2 2 1,
      .periodic 1 8 #[4, 5, 6, 7]]⟩ 2 10 = false := by decide +kernel

theorem extra_rows :
    Slices.matchesSource source ⟨#[.affine 2 2 1,
      .periodic 2 8 #[4, 5, 6, 7], .dense #[20]]⟩ 2 10 = false := by decide +kernel

theorem outside_source :
    Slices.matchesSource source selected 99 10 = false := by decide +kernel

import_setup_source smokeSource from "artifacts/setup/decoder-smoke.json"
import_setup_column smokeRange from "artifacts/setup/decoder-smoke.json"
  native_table_id 26 physical_column 0 source_bytes smokeSource

theorem imported_column_geometry :
    smokeRangeRegion.id = 26 ∧ smokeRangeRegion.offset = 1 ∧
      smokeRangeRegion.length = 8192 ∧ smokeRangePhysicalColumn = 0 := by decide +kernel

theorem imported_column_values :
    smokeRange.get? 0 = some 0 ∧ smokeRange.get? 8191 = some 8191 := by decide +kernel

/-- error: setup table ID 999999 is absent -/
#guard_msgs in
import_setup_column missingRegion from "artifacts/setup/decoder-smoke.json"
  native_table_id 999999 physical_column 0 source_bytes smokeSource

/-- error: setup physical column is absent -/
#guard_msgs in
import_setup_column missingColumn from "artifacts/setup/decoder-smoke.json"
  native_table_id 26 physical_column 999 source_bytes smokeSource

def wrongSource : String := "{}"

/-- error: shared setup source bytes differ from the artifact -/
#guard_msgs in
import_setup_column wrongBytes from "artifacts/setup/decoder-smoke.json"
  native_table_id 26 physical_column 0 source_bytes wrongSource

def nonLiteralSource : String := "a" ++ "b"

/-- error: shared setup source must be an imported literal string -/
#guard_msgs in
import_setup_column nonLiteral from "artifacts/setup/decoder-smoke.json"
  native_table_id 26 physical_column 0 source_bytes nonLiteralSource

end Tests.SetupRegionImport
