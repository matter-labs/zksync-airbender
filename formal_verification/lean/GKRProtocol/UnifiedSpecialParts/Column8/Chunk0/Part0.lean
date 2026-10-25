import GKRProtocol.UnifiedSpecialParts.Column8.Chunk0.Foundation

namespace Airbender.Compiler.UnifiedSpecialChunks.Column8.Chunk0
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

noncomputable def source0 : Setup.Block := original.get ⟨0, by decide +kernel⟩

column_blocks_part part0_0 from (UnifiedReduced.Setup.nativeZeroData.columns[(8 : Nat)]) start 0 stop 1
noncomputable def destination0_0 : Setup.Block := part0_0.get ⟨0, by decide +kernel⟩

column_blocks_part part0_1 from (UnifiedReduced.Setup.nativeRegisterZeroData.columns[(8 : Nat)]) start 0 stop 1
noncomputable def destination0_1 : Setup.Block := part0_1.get ⟨0, by decide +kernel⟩

column_blocks_part part0_2 from (UnifiedReduced.Setup.nativeCleanupData.columns[(8 : Nat)]) start 0 stop 1
noncomputable def destination0_2 : Setup.Block := part0_2.get ⟨0, by decide +kernel⟩

column_blocks_part part0_3 from (UnifiedReduced.Setup.nativeByteSignData.columns[(8 : Nat)]) start 0 stop 1
noncomputable def destination0_3 : Setup.Block := part0_3.get ⟨0, by decide +kernel⟩

column_blocks_part part0_4 from (UnifiedReduced.Setup.nativeSignData.columns[(8 : Nat)]) start 0 stop 1
noncomputable def destination0_4 : Setup.Block := part0_4.get ⟨0, by decide +kernel⟩

column_blocks_part part0_5 from (UnifiedReduced.Setup.nativeTruncationData.columns[(8 : Nat)]) start 0 stop 1
noncomputable def destination0_5 : Setup.Block := part0_5.get ⟨0, by decide +kernel⟩

column_blocks_part part0_6 from (UnifiedReduced.Setup.nativeShiftData.columns[(8 : Nat)]) start 0 stop 1
noncomputable def destination0_6 : Setup.Block := part0_6.get ⟨0, by decide +kernel⟩

column_blocks_part part0_7 from (UnifiedReduced.Setup.nativeROMData.columns[(8 : Nat)]) start 0 stop 1
noncomputable def destination0_7 : Setup.Block := part0_7.get ⟨0, by decide +kernel⟩

column_blocks_part part0_8 from (UnifiedReduced.Setup.nativeRotate16Data.columns[(8 : Nat)]) start 0 stop 1
noncomputable def destination0_8 : Setup.Block := part0_8.get ⟨0, by decide +kernel⟩

column_blocks_part part0_9 from (UnifiedReduced.Setup.nativeRotate12Data.columns[(8 : Nat)]) start 0 stop 1
noncomputable def destination0_9 : Setup.Block := part0_9.get ⟨0, by decide +kernel⟩

column_blocks_part part0_10 from (UnifiedReduced.Setup.nativeRotate8Data.columns[(8 : Nat)]) start 0 stop 1
noncomputable def destination0_10 : Setup.Block := part0_10.get ⟨0, by decide +kernel⟩

column_blocks_part part0_11 from (UnifiedReduced.Setup.nativeRotate7Data.columns[(8 : Nat)]) start 0 stop 1
noncomputable def destination0_11 : Setup.Block := part0_11.get ⟨0, by decide +kernel⟩

column_blocks_part part0_12 from (UnifiedReduced.Setup.nativeConditionalData.columns[(8 : Nat)]) start 0 stop 1
noncomputable def destination0_12 : Setup.Block := part0_12.get ⟨0, by decide +kernel⟩

column_blocks_part part0_13 from (UnifiedReduced.Setup.nativeXorData.columns[(8 : Nat)]) start 0 stop 1
noncomputable def destination0_13 : Setup.Block := part0_13.get ⟨0, by decide +kernel⟩

column_blocks_part part0_14 from (UnifiedReduced.Setup.nativeOrData.columns[(8 : Nat)]) start 0 stop 1
noncomputable def destination0_14 : Setup.Block := part0_14.get ⟨0, by decide +kernel⟩

column_blocks_part part0_15 from (UnifiedReduced.Setup.nativeAndData.columns[(8 : Nat)]) start 0 stop 1
noncomputable def destination0_15 : Setup.Block := part0_15.get ⟨0, by decide +kernel⟩

noncomputable def target0 : List Setup.Block := part0_0 ++ part0_1 ++ part0_2 ++ part0_3 ++ part0_4 ++ part0_5 ++ part0_6 ++ part0_7 ++ part0_8 ++ part0_9 ++ part0_10 ++ part0_11 ++ part0_12 ++ part0_13 ++ part0_14 ++ part0_15

theorem follows0 : blockTargetsFollow source0 0 target0 :=
  And.intro (by
    intro index bounded
    change source0.get? (0 + index) = destination0_0.get? index
    change (Setup.Block.affine 2097537 0 0).get? (0 + index) = (Setup.Block.affine 1 0 0).get? index
    apply affine_block_span
    · exact (by have bound : index < 1 := bounded; omega : 0 + index < 2097537)
    · exact (show index < 1 from bounded)
    · decide +kernel
  ) (And.intro (by
    intro index bounded
    change source0.get? (1 + index) = destination0_1.get? index
    change (Setup.Block.affine 2097537 0 0).get? (1 + index) = (Setup.Block.affine 131072 0 0).get? index
    apply affine_block_span
    · exact (by have bound : index < 131072 := bounded; omega : 1 + index < 2097537)
    · exact (show index < 131072 from bounded)
    · decide +kernel
  ) (And.intro (by
    intro index bounded
    change source0.get? (131073 + index) = destination0_2.get? index
    change (Setup.Block.affine 2097537 0 0).get? (131073 + index) = (Setup.Block.affine 65536 0 0).get? index
    apply affine_block_span
    · exact (by have bound : index < 65536 := bounded; omega : 131073 + index < 2097537)
    · exact (show index < 65536 from bounded)
    · decide +kernel
  ) (And.intro (by
    intro index bounded
    change source0.get? (196609 + index) = destination0_3.get? index
    change (Setup.Block.affine 2097537 0 0).get? (196609 + index) = (Setup.Block.affine 256 0 0).get? index
    apply affine_block_span
    · exact (by have bound : index < 256 := bounded; omega : 196609 + index < 2097537)
    · exact (show index < 256 from bounded)
    · decide +kernel
  ) (And.intro (by
    intro index bounded
    change source0.get? (196865 + index) = destination0_4.get? index
    change (Setup.Block.affine 2097537 0 0).get? (196865 + index) = (Setup.Block.affine 65536 0 0).get? index
    apply affine_block_span
    · exact (by have bound : index < 65536 := bounded; omega : 196865 + index < 2097537)
    · exact (show index < 65536 from bounded)
    · decide +kernel
  ) (And.intro (by
    intro index bounded
    change source0.get? (262401 + index) = destination0_5.get? index
    change (Setup.Block.affine 2097537 0 0).get? (262401 + index) = (Setup.Block.affine 65536 0 0).get? index
    apply affine_block_span
    · exact (by have bound : index < 65536 := bounded; omega : 262401 + index < 2097537)
    · exact (show index < 65536 from bounded)
    · decide +kernel
  ) (And.intro (by
    intro index bounded
    change source0.get? (327937 + index) = destination0_6.get? index
    change (Setup.Block.affine 2097537 0 0).get? (327937 + index) = (Setup.Block.affine 262144 0 0).get? index
    apply affine_block_span
    · exact (by have bound : index < 262144 := bounded; omega : 327937 + index < 2097537)
    · exact (show index < 262144 from bounded)
    · decide +kernel
  ) (And.intro (by
    intro index bounded
    change source0.get? (590081 + index) = destination0_7.get? index
    change (Setup.Block.affine 2097537 0 0).get? (590081 + index) = (Setup.Block.affine 1048576 0 0).get? index
    apply affine_block_span
    · exact (by have bound : index < 1048576 := bounded; omega : 590081 + index < 2097537)
    · exact (show index < 1048576 from bounded)
    · decide +kernel
  ) (And.intro (by
    intro index bounded
    change source0.get? (1638657 + index) = destination0_8.get? index
    change (Setup.Block.affine 2097537 0 0).get? (1638657 + index) = (Setup.Block.affine 65536 0 0).get? index
    apply affine_block_span
    · exact (by have bound : index < 65536 := bounded; omega : 1638657 + index < 2097537)
    · exact (show index < 65536 from bounded)
    · decide +kernel
  ) (And.intro (by
    intro index bounded
    change source0.get? (1704193 + index) = destination0_9.get? index
    change (Setup.Block.affine 2097537 0 0).get? (1704193 + index) = (Setup.Block.affine 65536 0 0).get? index
    apply affine_block_span
    · exact (by have bound : index < 65536 := bounded; omega : 1704193 + index < 2097537)
    · exact (show index < 65536 from bounded)
    · decide +kernel
  ) (And.intro (by
    intro index bounded
    change source0.get? (1769729 + index) = destination0_10.get? index
    change (Setup.Block.affine 2097537 0 0).get? (1769729 + index) = (Setup.Block.affine 65536 0 0).get? index
    apply affine_block_span
    · exact (by have bound : index < 65536 := bounded; omega : 1769729 + index < 2097537)
    · exact (show index < 65536 from bounded)
    · decide +kernel
  ) (And.intro (by
    intro index bounded
    change source0.get? (1835265 + index) = destination0_11.get? index
    change (Setup.Block.affine 2097537 0 0).get? (1835265 + index) = (Setup.Block.affine 65536 0 0).get? index
    apply affine_block_span
    · exact (by have bound : index < 65536 := bounded; omega : 1835265 + index < 2097537)
    · exact (show index < 65536 from bounded)
    · decide +kernel
  ) (And.intro (by
    intro index bounded
    change source0.get? (1900801 + index) = destination0_12.get? index
    change (Setup.Block.affine 2097537 0 0).get? (1900801 + index) = (Setup.Block.affine 128 0 0).get? index
    apply affine_block_span
    · exact (by have bound : index < 128 := bounded; omega : 1900801 + index < 2097537)
    · exact (show index < 128 from bounded)
    · decide +kernel
  ) (And.intro (by
    intro index bounded
    change source0.get? (1900929 + index) = destination0_13.get? index
    change (Setup.Block.affine 2097537 0 0).get? (1900929 + index) = (Setup.Block.affine 65536 0 0).get? index
    apply affine_block_span
    · exact (by have bound : index < 65536 := bounded; omega : 1900929 + index < 2097537)
    · exact (show index < 65536 from bounded)
    · decide +kernel
  ) (And.intro (by
    intro index bounded
    change source0.get? (1966465 + index) = destination0_14.get? index
    change (Setup.Block.affine 2097537 0 0).get? (1966465 + index) = (Setup.Block.affine 65536 0 0).get? index
    apply affine_block_span
    · exact (by have bound : index < 65536 := bounded; omega : 1966465 + index < 2097537)
    · exact (show index < 65536 from bounded)
    · decide +kernel
  ) (And.intro (by
    intro index bounded
    change source0.get? (2032001 + index) = destination0_15.get? index
    change (Setup.Block.affine 2097537 0 0).get? (2032001 + index) = (Setup.Block.affine 65536 0 0).get? index
    apply affine_block_span
    · exact (by have bound : index < 65536 := bounded; omega : 2032001 + index < 2097537)
    · exact (show index < 65536 from bounded)
    · decide +kernel
  ) (True.intro))))))))))))))))

theorem length0 : (target0.map Setup.Block.length).sum = source0.length := by decide +kernel

end Airbender.Compiler.UnifiedSpecialChunks.Column8.Chunk0
