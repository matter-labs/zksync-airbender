import Airbender.Proofs.GKRProtocol.UnifiedPackedEqualityData

namespace Airbender.Compiler.UnifiedPackedEquality
open Airbender Airbender.Compiler.PackedSetupEquality
set_option warningAsError true
-- The kernel compares all 2,584 numeric block records in one Boolean fact.
set_option maxRecDepth 131072

theorem ok : PackedSetupEquality.checkWithLengths sourceCode targetCode lengthChecks = true := by decide +kernel

theorem fixed_column_blocks :
    (Data.GKRSetup.Unified.setupColumn2.blocks.toList.drop 128).take 2584 =
    (UnifiedReduced.Setup.nativeXorData.columns[2].blocks.toList.drop 111).take 788 ++
    UnifiedReduced.Setup.nativeOrData.columns[2].blocks.toList ++
    UnifiedReduced.Setup.nativeAndData.columns[2].blocks.toList := by
  rw [source_binding, target_binding]
  exact (PackedSetupEquality.checkWithLengths_sound _ _ _ ok).1

/-- The same Boolean result proves every former row-count conclusion. -/
theorem row_counts (item : LengthCheck) (member : item ∈ lengthChecks) :
    (((((Data.GKRSetup.Unified.setupColumn2.blocks.toList.drop 128).take 2584).drop item.first).take item.count).map Setup.Block.length).sum = item.expected := by
  rw [source_binding]
  exact (PackedSetupEquality.checkWithLengths_sound _ _ _ ok).2 item member

end Airbender.Compiler.UnifiedPackedEquality
