import Airbender.Import.Embed
import Airbender.Review.Helpers.Sail

namespace Airbender.JumpBranchSlt

namespace Branch
def funct3 (opcode : SailRV32.bop) : Nat :=
  match opcode with
  | .BEQ => 0 | .BNE => 1 | .BLT => 4 | .BGE => 5 | .BLTU => 6 | .BGEU => 7

end Branch

-- Retained assertions, word/comparison queries and native trace metadata.
-- Fixed-table correspondence and logical matching enforcement remain external.
import_clean importedConstraints from "../../cs/compiled_circuits/jump_branch_slt_layout_no_caches_gkr.json" comparison_lookups trace_metadata

/-- Original retained constraints plus the eight native timestamp queries. -/
def clockConstraints {p : Nat} [Fact p.Prime] : List (FlatOperation (ZMod p)) :=
  importedConstraints ++ importedConstraintsTimestampLookups

-- Named columns used by the review contracts. ArtifactChecks verifies their
-- locations; the decoder interface supplies the selectors' meaning.
namespace Variables
abbrev initialPCLo : Nat := 0
abbrev initialPCHi : Nat := 1
abbrev execute : Nat := 4
abbrev rs1Index : Nat := 5
abbrev rs2Index : Nat := 6
abbrev rdIndex : Nat := 7
abbrev immediateLo : Nat := 8
abbrev immediateHi : Nat := 9
abbrev conditionTag : Nat := 10
abbrev jalSelector : Nat := 11
abbrev jalrSelector : Nat := 12
abbrev comparisonSelector : Nat := 13
abbrev branchSelector : Nat := 14
abbrev discardedSelector : Nat := 15
abbrev finalPCLo : Nat := 16
abbrev finalPCHi : Nat := 17
abbrev rs1Lo : Nat := 22
abbrev rs1Hi : Nat := 23
abbrev rs2Lo : Nat := 26
abbrev rs2Hi : Nat := 27
abbrev destinationLo : Nat := 30
abbrev destinationHi : Nat := 31
end Variables

end Airbender.JumpBranchSlt
