import GKRProtocol.UnifiedPrefixParts.Column1.Foundation

namespace Airbender.Compiler.UnifiedPrefixNative.Column1
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

noncomputable def source14 : Setup.Block := original.get ⟨14, by decide +kernel⟩

column_blocks_part part14_0 from (UnifiedReduced.Setup.nativeRotate16Data.columns[(1 : Nat)]) start 1 stop 2
noncomputable def destination14_0 : Setup.Block := part14_0.get ⟨0, by decide +kernel⟩

column_blocks_part part14_1 from (UnifiedReduced.Setup.nativeRotate16Data.columns[(1 : Nat)]) start 2 stop 3
noncomputable def destination14_1 : Setup.Block := part14_1.get ⟨0, by decide +kernel⟩

column_blocks_part part14_2 from (UnifiedReduced.Setup.nativeRotate12Data.columns[(1 : Nat)]) start 0 stop 1
noncomputable def destination14_2 : Setup.Block := part14_2.get ⟨0, by decide +kernel⟩

column_blocks_part part14_3 from (UnifiedReduced.Setup.nativeRotate12Data.columns[(1 : Nat)]) start 1 stop 2
noncomputable def destination14_3 : Setup.Block := part14_3.get ⟨0, by decide +kernel⟩

column_blocks_part part14_4 from (UnifiedReduced.Setup.nativeRotate12Data.columns[(1 : Nat)]) start 2 stop 3
noncomputable def destination14_4 : Setup.Block := part14_4.get ⟨0, by decide +kernel⟩

column_blocks_part part14_5 from (UnifiedReduced.Setup.nativeRotate8Data.columns[(1 : Nat)]) start 0 stop 1
noncomputable def destination14_5 : Setup.Block := part14_5.get ⟨0, by decide +kernel⟩

column_blocks_part part14_6 from (UnifiedReduced.Setup.nativeRotate8Data.columns[(1 : Nat)]) start 1 stop 2
noncomputable def destination14_6 : Setup.Block := part14_6.get ⟨0, by decide +kernel⟩

column_blocks_part part14_7 from (UnifiedReduced.Setup.nativeRotate8Data.columns[(1 : Nat)]) start 2 stop 3
noncomputable def destination14_7 : Setup.Block := part14_7.get ⟨0, by decide +kernel⟩

column_blocks_part part14_8 from (UnifiedReduced.Setup.nativeRotate7Data.columns[(1 : Nat)]) start 0 stop 1
noncomputable def destination14_8 : Setup.Block := part14_8.get ⟨0, by decide +kernel⟩

column_blocks_part part14_9 from (UnifiedReduced.Setup.nativeRotate7Data.columns[(1 : Nat)]) start 1 stop 2
noncomputable def destination14_9 : Setup.Block := part14_9.get ⟨0, by decide +kernel⟩

column_blocks_part part14_10 from (UnifiedReduced.Setup.nativeRotate7Data.columns[(1 : Nat)]) start 2 stop 3
noncomputable def destination14_10 : Setup.Block := part14_10.get ⟨0, by decide +kernel⟩

column_blocks_part part14_11 from (UnifiedReduced.Setup.nativeConditionalData.columns[(1 : Nat)]) start 0 stop 1
noncomputable def destination14_11 : Setup.Block := part14_11.get ⟨0, by decide +kernel⟩

noncomputable def target14 : List Setup.Block := part14_0 ++ part14_1 ++ part14_2 ++ part14_3 ++ part14_4 ++ part14_5 ++ part14_6 ++ part14_7 ++ part14_8 ++ part14_9 ++ part14_10 ++ part14_11

set_option maxHeartbeats 16000000 in
theorem follows14 : blockTargetsFollow source14 0 target14 :=
  And.intro (by
    intro index bounded
    change source14.get? (0 + index) = destination14_0.get? index
    change (Setup.Block.periodic 1024 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 0]).get? (0 + index) =
      (Setup.Block.periodic 255 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 0]).get? index
    apply periodic_zero_block_span
    · exact (by have bound : index < 65280 := bounded; omega : 0 + index < 262144)
    · exact (show index < 65280 from bounded)
    · exact (by decide +kernel : 0 % 256 = 0)
  ) (And.intro (by
    intro index bounded
    change source14.get? (65280 + index) = destination14_1.get? index
    have checked0 : finiteBlockSpanRangeCheck source14 destination14_1 65280 0 32 = true := by decide +kernel
    have checked32 : finiteBlockSpanRangeCheck source14 destination14_1 65280 32 32 = true := by decide +kernel
    have checked64 : finiteBlockSpanRangeCheck source14 destination14_1 65280 64 32 = true := by decide +kernel
    have checked96 : finiteBlockSpanRangeCheck source14 destination14_1 65280 96 32 = true := by decide +kernel
    have checked128 : finiteBlockSpanRangeCheck source14 destination14_1 65280 128 32 = true := by decide +kernel
    have checked160 : finiteBlockSpanRangeCheck source14 destination14_1 65280 160 32 = true := by decide +kernel
    have checked192 : finiteBlockSpanRangeCheck source14 destination14_1 65280 192 32 = true := by decide +kernel
    have checked224 : finiteBlockSpanRangeCheck source14 destination14_1 65280 224 31 = true := by decide +kernel
    by_cases before0 : index < 32
    · exact finite_block_span_range_sound source14 destination14_1 65280 0 32 checked0 index (by omega) (by have : index < 255 := bounded; omega)
    ·
      by_cases before32 : index < 64
      · exact finite_block_span_range_sound source14 destination14_1 65280 32 32 checked32 index (by omega) (by have : index < 255 := bounded; omega)
      ·
        by_cases before64 : index < 96
        · exact finite_block_span_range_sound source14 destination14_1 65280 64 32 checked64 index (by omega) (by have : index < 255 := bounded; omega)
        ·
          by_cases before96 : index < 128
          · exact finite_block_span_range_sound source14 destination14_1 65280 96 32 checked96 index (by omega) (by have : index < 255 := bounded; omega)
          ·
            by_cases before128 : index < 160
            · exact finite_block_span_range_sound source14 destination14_1 65280 128 32 checked128 index (by omega) (by have : index < 255 := bounded; omega)
            ·
              by_cases before160 : index < 192
              · exact finite_block_span_range_sound source14 destination14_1 65280 160 32 checked160 index (by omega) (by have : index < 255 := bounded; omega)
              ·
                by_cases before192 : index < 224
                · exact finite_block_span_range_sound source14 destination14_1 65280 192 32 checked192 index (by omega) (by have : index < 255 := bounded; omega)
                ·
                  exact finite_block_span_range_sound source14 destination14_1 65280 224 31 checked224 index (by omega) (by have : index < 255 := bounded; omega)
  ) (And.intro (by
    intro index bounded
    change source14.get? (65535 + index) = destination14_2.get? index
    have checked : finiteBlockSpanRangeCheck source14 destination14_2 65535 0 1 = true := by decide +kernel
    exact finite_block_span_range_sound source14 destination14_2 65535 0 1 checked index (by omega) (by have : index < 1 := bounded; omega)
  ) (And.intro (by
    intro index bounded
    change source14.get? (65536 + index) = destination14_3.get? index
    change (Setup.Block.periodic 1024 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 0]).get? (65536 + index) =
      (Setup.Block.periodic 255 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 0]).get? index
    apply periodic_zero_block_span
    · exact (by have bound : index < 65280 := bounded; omega : 65536 + index < 262144)
    · exact (show index < 65280 from bounded)
    · exact (by decide +kernel : 65536 % 256 = 0)
  ) (And.intro (by
    intro index bounded
    change source14.get? (130816 + index) = destination14_4.get? index
    have checked0 : finiteBlockSpanRangeCheck source14 destination14_4 130816 0 32 = true := by decide +kernel
    have checked32 : finiteBlockSpanRangeCheck source14 destination14_4 130816 32 32 = true := by decide +kernel
    have checked64 : finiteBlockSpanRangeCheck source14 destination14_4 130816 64 32 = true := by decide +kernel
    have checked96 : finiteBlockSpanRangeCheck source14 destination14_4 130816 96 32 = true := by decide +kernel
    have checked128 : finiteBlockSpanRangeCheck source14 destination14_4 130816 128 32 = true := by decide +kernel
    have checked160 : finiteBlockSpanRangeCheck source14 destination14_4 130816 160 32 = true := by decide +kernel
    have checked192 : finiteBlockSpanRangeCheck source14 destination14_4 130816 192 32 = true := by decide +kernel
    have checked224 : finiteBlockSpanRangeCheck source14 destination14_4 130816 224 31 = true := by decide +kernel
    by_cases before0 : index < 32
    · exact finite_block_span_range_sound source14 destination14_4 130816 0 32 checked0 index (by omega) (by have : index < 255 := bounded; omega)
    ·
      by_cases before32 : index < 64
      · exact finite_block_span_range_sound source14 destination14_4 130816 32 32 checked32 index (by omega) (by have : index < 255 := bounded; omega)
      ·
        by_cases before64 : index < 96
        · exact finite_block_span_range_sound source14 destination14_4 130816 64 32 checked64 index (by omega) (by have : index < 255 := bounded; omega)
        ·
          by_cases before96 : index < 128
          · exact finite_block_span_range_sound source14 destination14_4 130816 96 32 checked96 index (by omega) (by have : index < 255 := bounded; omega)
          ·
            by_cases before128 : index < 160
            · exact finite_block_span_range_sound source14 destination14_4 130816 128 32 checked128 index (by omega) (by have : index < 255 := bounded; omega)
            ·
              by_cases before160 : index < 192
              · exact finite_block_span_range_sound source14 destination14_4 130816 160 32 checked160 index (by omega) (by have : index < 255 := bounded; omega)
              ·
                by_cases before192 : index < 224
                · exact finite_block_span_range_sound source14 destination14_4 130816 192 32 checked192 index (by omega) (by have : index < 255 := bounded; omega)
                ·
                  exact finite_block_span_range_sound source14 destination14_4 130816 224 31 checked224 index (by omega) (by have : index < 255 := bounded; omega)
  ) (And.intro (by
    intro index bounded
    change source14.get? (131071 + index) = destination14_5.get? index
    have checked : finiteBlockSpanRangeCheck source14 destination14_5 131071 0 1 = true := by decide +kernel
    exact finite_block_span_range_sound source14 destination14_5 131071 0 1 checked index (by omega) (by have : index < 1 := bounded; omega)
  ) (And.intro (by
    intro index bounded
    change source14.get? (131072 + index) = destination14_6.get? index
    change (Setup.Block.periodic 1024 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 0]).get? (131072 + index) =
      (Setup.Block.periodic 255 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 0]).get? index
    apply periodic_zero_block_span
    · exact (by have bound : index < 65280 := bounded; omega : 131072 + index < 262144)
    · exact (show index < 65280 from bounded)
    · exact (by decide +kernel : 131072 % 256 = 0)
  ) (And.intro (by
    intro index bounded
    change source14.get? (196352 + index) = destination14_7.get? index
    have checked0 : finiteBlockSpanRangeCheck source14 destination14_7 196352 0 32 = true := by decide +kernel
    have checked32 : finiteBlockSpanRangeCheck source14 destination14_7 196352 32 32 = true := by decide +kernel
    have checked64 : finiteBlockSpanRangeCheck source14 destination14_7 196352 64 32 = true := by decide +kernel
    have checked96 : finiteBlockSpanRangeCheck source14 destination14_7 196352 96 32 = true := by decide +kernel
    have checked128 : finiteBlockSpanRangeCheck source14 destination14_7 196352 128 32 = true := by decide +kernel
    have checked160 : finiteBlockSpanRangeCheck source14 destination14_7 196352 160 32 = true := by decide +kernel
    have checked192 : finiteBlockSpanRangeCheck source14 destination14_7 196352 192 32 = true := by decide +kernel
    have checked224 : finiteBlockSpanRangeCheck source14 destination14_7 196352 224 31 = true := by decide +kernel
    by_cases before0 : index < 32
    · exact finite_block_span_range_sound source14 destination14_7 196352 0 32 checked0 index (by omega) (by have : index < 255 := bounded; omega)
    ·
      by_cases before32 : index < 64
      · exact finite_block_span_range_sound source14 destination14_7 196352 32 32 checked32 index (by omega) (by have : index < 255 := bounded; omega)
      ·
        by_cases before64 : index < 96
        · exact finite_block_span_range_sound source14 destination14_7 196352 64 32 checked64 index (by omega) (by have : index < 255 := bounded; omega)
        ·
          by_cases before96 : index < 128
          · exact finite_block_span_range_sound source14 destination14_7 196352 96 32 checked96 index (by omega) (by have : index < 255 := bounded; omega)
          ·
            by_cases before128 : index < 160
            · exact finite_block_span_range_sound source14 destination14_7 196352 128 32 checked128 index (by omega) (by have : index < 255 := bounded; omega)
            ·
              by_cases before160 : index < 192
              · exact finite_block_span_range_sound source14 destination14_7 196352 160 32 checked160 index (by omega) (by have : index < 255 := bounded; omega)
              ·
                by_cases before192 : index < 224
                · exact finite_block_span_range_sound source14 destination14_7 196352 192 32 checked192 index (by omega) (by have : index < 255 := bounded; omega)
                ·
                  exact finite_block_span_range_sound source14 destination14_7 196352 224 31 checked224 index (by omega) (by have : index < 255 := bounded; omega)
  ) (And.intro (by
    intro index bounded
    change source14.get? (196607 + index) = destination14_8.get? index
    have checked : finiteBlockSpanRangeCheck source14 destination14_8 196607 0 1 = true := by decide +kernel
    exact finite_block_span_range_sound source14 destination14_8 196607 0 1 checked index (by omega) (by have : index < 1 := bounded; omega)
  ) (And.intro (by
    intro index bounded
    change source14.get? (196608 + index) = destination14_9.get? index
    change (Setup.Block.periodic 1024 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 0]).get? (196608 + index) =
      (Setup.Block.periodic 255 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 0]).get? index
    apply periodic_zero_block_span
    · exact (by have bound : index < 65280 := bounded; omega : 196608 + index < 262144)
    · exact (show index < 65280 from bounded)
    · exact (by decide +kernel : 196608 % 256 = 0)
  ) (And.intro (by
    intro index bounded
    change source14.get? (261888 + index) = destination14_10.get? index
    have checked0 : finiteBlockSpanRangeCheck source14 destination14_10 261888 0 32 = true := by decide +kernel
    have checked32 : finiteBlockSpanRangeCheck source14 destination14_10 261888 32 32 = true := by decide +kernel
    have checked64 : finiteBlockSpanRangeCheck source14 destination14_10 261888 64 32 = true := by decide +kernel
    have checked96 : finiteBlockSpanRangeCheck source14 destination14_10 261888 96 32 = true := by decide +kernel
    have checked128 : finiteBlockSpanRangeCheck source14 destination14_10 261888 128 32 = true := by decide +kernel
    have checked160 : finiteBlockSpanRangeCheck source14 destination14_10 261888 160 32 = true := by decide +kernel
    have checked192 : finiteBlockSpanRangeCheck source14 destination14_10 261888 192 32 = true := by decide +kernel
    have checked224 : finiteBlockSpanRangeCheck source14 destination14_10 261888 224 31 = true := by decide +kernel
    by_cases before0 : index < 32
    · exact finite_block_span_range_sound source14 destination14_10 261888 0 32 checked0 index (by omega) (by have : index < 255 := bounded; omega)
    ·
      by_cases before32 : index < 64
      · exact finite_block_span_range_sound source14 destination14_10 261888 32 32 checked32 index (by omega) (by have : index < 255 := bounded; omega)
      ·
        by_cases before64 : index < 96
        · exact finite_block_span_range_sound source14 destination14_10 261888 64 32 checked64 index (by omega) (by have : index < 255 := bounded; omega)
        ·
          by_cases before96 : index < 128
          · exact finite_block_span_range_sound source14 destination14_10 261888 96 32 checked96 index (by omega) (by have : index < 255 := bounded; omega)
          ·
            by_cases before128 : index < 160
            · exact finite_block_span_range_sound source14 destination14_10 261888 128 32 checked128 index (by omega) (by have : index < 255 := bounded; omega)
            ·
              by_cases before160 : index < 192
              · exact finite_block_span_range_sound source14 destination14_10 261888 160 32 checked160 index (by omega) (by have : index < 255 := bounded; omega)
              ·
                by_cases before192 : index < 224
                · exact finite_block_span_range_sound source14 destination14_10 261888 192 32 checked192 index (by omega) (by have : index < 255 := bounded; omega)
                ·
                  exact finite_block_span_range_sound source14 destination14_10 261888 224 31 checked224 index (by omega) (by have : index < 255 := bounded; omega)
  ) (And.intro (by
    intro index bounded
    change source14.get? (262143 + index) = destination14_11.get? index
    have checked : finiteBlockSpanRangeCheck source14 destination14_11 262143 0 1 = true := by decide +kernel
    exact finite_block_span_range_sound source14 destination14_11 262143 0 1 checked index (by omega) (by have : index < 1 := bounded; omega)
  ) (True.intro))))))))))))

theorem length14 : (target14.map Setup.Block.length).sum = source14.length := by decide +kernel

end Airbender.Compiler.UnifiedPrefixNative.Column1
