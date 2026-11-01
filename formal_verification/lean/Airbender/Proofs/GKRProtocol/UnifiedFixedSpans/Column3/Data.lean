import Airbender.Proofs.GKRProtocol.UnifiedSpecialParts.Column3.Chunk0.Foundation

set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072

namespace Airbender.Compiler.UnifiedSpecialChunks.Column3.Chunk0
open Airbender Airbender.Compiler

noncomputable def source0 : Setup.Block := original.get ⟨0, by decide +kernel⟩

column_blocks_part part0_0 from (UnifiedReduced.Setup.nativeZeroData.columns[(3 : Nat)]) start 0 stop 1
noncomputable def destination0_0 : Setup.Block := part0_0.get ⟨0, by decide +kernel⟩

column_blocks_part part0_1 from (UnifiedReduced.Setup.nativeRegisterZeroData.columns[(3 : Nat)]) start 0 stop 1
noncomputable def destination0_1 : Setup.Block := part0_1.get ⟨0, by decide +kernel⟩

column_blocks_part part0_2 from (UnifiedReduced.Setup.nativeCleanupData.columns[(3 : Nat)]) start 0 stop 1
noncomputable def destination0_2 : Setup.Block := part0_2.get ⟨0, by decide +kernel⟩

column_blocks_part part0_3 from (UnifiedReduced.Setup.nativeByteSignData.columns[(3 : Nat)]) start 0 stop 1
noncomputable def destination0_3 : Setup.Block := part0_3.get ⟨0, by decide +kernel⟩

column_blocks_part part0_4 from (UnifiedReduced.Setup.nativeSignData.columns[(3 : Nat)]) start 0 stop 1
noncomputable def destination0_4 : Setup.Block := part0_4.get ⟨0, by decide +kernel⟩

column_blocks_part part0_5 from (UnifiedReduced.Setup.nativeTruncationData.columns[(3 : Nat)]) start 0 stop 1
noncomputable def destination0_5 : Setup.Block := part0_5.get ⟨0, by decide +kernel⟩

column_blocks_part part0_6 from (UnifiedReduced.Setup.nativeShiftData.columns[(3 : Nat)]) start 0 stop 1
noncomputable def destination0_6 : Setup.Block := part0_6.get ⟨0, by decide +kernel⟩

noncomputable def target0 : List Setup.Block := part0_0 ++ part0_1 ++ part0_2 ++ part0_3 ++ part0_4 ++ part0_5 ++ part0_6

noncomputable def source1 : Setup.Block := original.get ⟨1, by decide +kernel⟩

column_blocks_part part1_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(3 : Nat)]) start 1 stop 2
noncomputable def destination1_0 : Setup.Block := part1_0.get ⟨0, by decide +kernel⟩

column_blocks_part part1_1 from (UnifiedReduced.Setup.nativeShiftData.columns[(3 : Nat)]) start 2 stop 3
noncomputable def destination1_1 : Setup.Block := part1_1.get ⟨0, by decide +kernel⟩

column_blocks_part part1_2 from (UnifiedReduced.Setup.nativeROMData.columns[(3 : Nat)]) start 0 stop 1
noncomputable def destination1_2 : Setup.Block := part1_2.get ⟨0, by decide +kernel⟩

noncomputable def target1 : List Setup.Block := part1_0 ++ part1_1 ++ part1_2

noncomputable def source2 : Setup.Block := original.get ⟨2, by decide +kernel⟩

column_blocks_part part2_0 from (UnifiedReduced.Setup.nativeROMData.columns[(3 : Nat)]) start 1 stop 2
noncomputable def destination2_0 : Setup.Block := part2_0.get ⟨0, by decide +kernel⟩

column_blocks_part part2_1 from (UnifiedReduced.Setup.nativeRotate16Data.columns[(3 : Nat)]) start 0 stop 1
noncomputable def destination2_1 : Setup.Block := part2_1.get ⟨0, by decide +kernel⟩

column_blocks_part part2_2 from (UnifiedReduced.Setup.nativeRotate12Data.columns[(3 : Nat)]) start 0 stop 1
noncomputable def destination2_2 : Setup.Block := part2_2.get ⟨0, by decide +kernel⟩

column_blocks_part part2_3 from (UnifiedReduced.Setup.nativeRotate8Data.columns[(3 : Nat)]) start 0 stop 1
noncomputable def destination2_3 : Setup.Block := part2_3.get ⟨0, by decide +kernel⟩

column_blocks_part part2_4 from (UnifiedReduced.Setup.nativeRotate7Data.columns[(3 : Nat)]) start 0 stop 1
noncomputable def destination2_4 : Setup.Block := part2_4.get ⟨0, by decide +kernel⟩

column_blocks_part part2_5 from (UnifiedReduced.Setup.nativeConditionalData.columns[(3 : Nat)]) start 0 stop 1
noncomputable def destination2_5 : Setup.Block := part2_5.get ⟨0, by decide +kernel⟩

column_blocks_part part2_6 from (UnifiedReduced.Setup.nativeXorData.columns[(3 : Nat)]) start 0 stop 1
noncomputable def destination2_6 : Setup.Block := part2_6.get ⟨0, by decide +kernel⟩

column_blocks_part part2_7 from (UnifiedReduced.Setup.nativeOrData.columns[(3 : Nat)]) start 0 stop 1
noncomputable def destination2_7 : Setup.Block := part2_7.get ⟨0, by decide +kernel⟩

column_blocks_part part2_8 from (UnifiedReduced.Setup.nativeAndData.columns[(3 : Nat)]) start 0 stop 1
noncomputable def destination2_8 : Setup.Block := part2_8.get ⟨0, by decide +kernel⟩

noncomputable def part2_9 : List Setup.Block := [.dense #[0, 0, 0]]
noncomputable def destination2_9 : Setup.Block := part2_9.get ⟨0, by decide +kernel⟩

noncomputable def target2 : List Setup.Block := part2_0 ++ part2_1 ++ part2_2 ++ part2_3 ++ part2_4 ++ part2_5 ++ part2_6 ++ part2_7 ++ part2_8 ++ part2_9

end Airbender.Compiler.UnifiedSpecialChunks.Column3.Chunk0

