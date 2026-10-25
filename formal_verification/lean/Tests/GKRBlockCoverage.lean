import GKRProtocol.BlockCoverageImport

namespace Tests.GKRBlockCoverage
open Airbender Airbender.Compiler
set_option warningAsError true

def column : Setup.Column := ⟨#[.affine 3 10 1, .affine 2 13 1]⟩
def leading : List Setup.Block := [.affine 3 10 1]
def trailing : List Setup.Block := [.affine 2 13 1]

column_parts_cover complete from column parts [leading, trailing]

/-- error: column parts omit or duplicate blocks -/
#guard_msgs in
column_parts_cover missing from column parts [leading]

/-- error: column parts omit or duplicate blocks -/
#guard_msgs in
column_parts_cover duplicated from column parts [leading, trailing, leading]

theorem complete_retains_last_row : column.get? 4 = some 14 := by decide +kernel

theorem changed_part_changes_a_row :
    Setup.getFromBlocks [.affine 3 10 1, .affine 2 14 1] 4 ≠ column.get? 4 := by decide +kernel

end Tests.GKRBlockCoverage
