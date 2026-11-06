import Airbender.Proofs.ReducedMachine.NativeShiftTemplates

namespace Airbender.ReducedMachine.NativeShiftShapeProofs
open Setup Verification NativeFixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

-- Canonical block descriptions from the already certified standalone column shapes.
def column2Part2 : List Block :=
  [.affine 2048 0 32,
   .affine 2048 0 32,
   .affine 2048 0 32,
   .affine 2048 0 32,
   .affine 2048 0 32,
   .affine 2048 0 32,
   .affine 2048 0 32,
   .periodic 64 0 SllHighProofs.template6,
   .periodic 128 0 SllHighProofs.template7,
   .periodic 256 0 SllHighProofs.template8,
   .periodic 512 0 SllHighProofs.template9,
   .periodic 1024 0 SllHighProofs.template10,
   .periodic 2048 0 SllHighProofs.template11,
   .periodic 4096 0 SllHighProofs.template12,
   .periodic 8192 0 SllHighProofs.template13,
   .periodic 16384 0 SllHighProofs.template14,
   .periodic 32768 0 SllHighProofs.template15,
   .affine 65537 0 0,
   .periodic 32768 0 SrlHighProofs.template1,
   .periodic 16384 0 SrlHighProofs.template2,
   .periodic 8192 0 SrlHighProofs.template3,
   .periodic 4096 0 SrlHighProofs.template4,
   .periodic 2048 0 SrlHighProofs.template5,
   .periodic 1024 0 SrlHighProofs.template6,
   .periodic 512 0 SrlHighProofs.template7,
   .periodic 256 0 SrlHighProofs.template8,
   .periodic 128 0 SrlHighProofs.template9,
   .periodic 64 0 SrlHighProofs.template10,
   .affine 2047 32 32,
   .affine 2048 0 32,
   .affine 2048 0 32,
   .affine 2048 0 32,
   .affine 2048 0 32,
   .affine 2048 0 32,
   .affine 2048 0 32,
   .affine 2048 0 32,
   .affine 2048 0 32,
   .affine 2048 0 32,
   .affine 2048 0 32,
   .affine 2048 0 32,
   .affine 2048 0 32,
   .affine 2048 0 32,
   .affine 2048 0 32,
   .affine 2048 0 32,
   .affine 2048 0 32,
   .affine 2048 0 32,
   .affine 2048 0 32,
   .affine 2048 0 32,
   .affine 2048 0 32,
   .affine 2048 0 32,
   .affine 2048 0 32,
   .affine 2048 0 32,
   .affine 2048 0 32,
   .affine 2048 0 32,
   .affine 2048 0 32,
   .affine 2048 0 32,
   .affine 2048 0 32,
   .affine 2048 0 32,
   .affine 2048 0 32,
   .affine 2048 0 32,
   .affine 4096 0 16,
   .affine 4096 0 16,
   .affine 4096 0 16,
   .affine 4096 0 16]

/-- Assemble literal identities without comparing whole imported columns. -/
theorem blocks2Part2 :
    [dataT37Column2Block128,
     dataT37Column2Block129,
     dataT37Column2Block130,
     dataT37Column2Block131,
     dataT37Column2Block132,
     dataT37Column2Block133,
     dataT37Column2Block134,
     dataT37Column2Block135,
     dataT37Column2Block136,
     dataT37Column2Block137,
     dataT37Column2Block138,
     dataT37Column2Block139,
     dataT37Column2Block140,
     dataT37Column2Block141,
     dataT37Column2Block142,
     dataT37Column2Block143,
     dataT37Column2Block144,
     dataT37Column2Block145,
     dataT37Column2Block146,
     dataT37Column2Block147,
     dataT37Column2Block148,
     dataT37Column2Block149,
     dataT37Column2Block150,
     dataT37Column2Block151,
     dataT37Column2Block152,
     dataT37Column2Block153,
     dataT37Column2Block154,
     dataT37Column2Block155,
     dataT37Column2Block156,
     dataT37Column2Block157,
     dataT37Column2Block158,
     dataT37Column2Block159,
     dataT37Column2Block160,
     dataT37Column2Block161,
     dataT37Column2Block162,
     dataT37Column2Block163,
     dataT37Column2Block164,
     dataT37Column2Block165,
     dataT37Column2Block166,
     dataT37Column2Block167,
     dataT37Column2Block168,
     dataT37Column2Block169,
     dataT37Column2Block170,
     dataT37Column2Block171,
     dataT37Column2Block172,
     dataT37Column2Block173,
     dataT37Column2Block174,
     dataT37Column2Block175,
     dataT37Column2Block176,
     dataT37Column2Block177,
     dataT37Column2Block178,
     dataT37Column2Block179,
     dataT37Column2Block180,
     dataT37Column2Block181,
     dataT37Column2Block182,
     dataT37Column2Block183,
     dataT37Column2Block184,
     dataT37Column2Block185,
     dataT37Column2Block186,
     dataT37Column2Block187,
     dataT37Column2Block188,
     dataT37Column2Block189,
     dataT37Column2Block190,
     dataT37Column2Block191] = column2Part2 := by
  exact (congrArg₂ List.cons (show dataT37Column2Block128 = (.affine 2048 0 32 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block129 = (.affine 2048 0 32 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block130 = (.affine 2048 0 32 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block131 = (.affine 2048 0 32 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block132 = (.affine 2048 0 32 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block133 = (.affine 2048 0 32 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block134 = (.affine 2048 0 32 : Block) from rfl)
      (congrArg₂ List.cons (Eq.trans (show dataT37Column2Block135 = dataT37Column1Block63 from rfl) NativeShiftTemplateL6Proofs.block)
      (congrArg₂ List.cons (Eq.trans (show dataT37Column2Block136 = dataT37Column1Block64 from rfl) NativeShiftTemplateL7Proofs.block)
      (congrArg₂ List.cons (Eq.trans (show dataT37Column2Block137 = dataT37Column1Block65 from rfl) NativeShiftTemplateL8Proofs.block)
      (congrArg₂ List.cons (Eq.trans (show dataT37Column2Block138 = dataT37Column1Block66 from rfl) NativeShiftTemplateL9Proofs.block)
      (congrArg₂ List.cons (Eq.trans (show dataT37Column2Block139 = dataT37Column1Block67 from rfl) NativeShiftTemplateL10Proofs.block)
      (congrArg₂ List.cons (Eq.trans (show dataT37Column2Block140 = dataT37Column1Block68 from rfl) NativeShiftTemplateL11Proofs.block)
      (congrArg₂ List.cons (Eq.trans (show dataT37Column2Block141 = dataT37Column1Block69 from rfl) NativeShiftTemplateL12Proofs.block)
      (congrArg₂ List.cons (Eq.trans (show dataT37Column2Block142 = dataT37Column1Block70 from rfl) NativeShiftTemplateL13Proofs.block)
      (congrArg₂ List.cons (Eq.trans (show dataT37Column2Block143 = dataT37Column1Block71 from rfl) NativeShiftTemplateL14Proofs.block)
      (congrArg₂ List.cons (Eq.trans (show dataT37Column2Block144 = dataT37Column1Block72 from rfl) NativeShiftTemplateL15Proofs.block)
      (congrArg₂ List.cons (show dataT37Column2Block145 = (.affine 65537 0 0 : Block) from rfl)
      (congrArg₂ List.cons NativeShiftTemplateR1Proofs.block
      (congrArg₂ List.cons NativeShiftTemplateR2Proofs.block
      (congrArg₂ List.cons NativeShiftTemplateR3Proofs.block
      (congrArg₂ List.cons NativeShiftTemplateR4Proofs.block
      (congrArg₂ List.cons NativeShiftTemplateR5Proofs.block
      (congrArg₂ List.cons NativeShiftTemplateR6Proofs.block
      (congrArg₂ List.cons NativeShiftTemplateR7Proofs.block
      (congrArg₂ List.cons NativeShiftTemplateR8Proofs.block
      (congrArg₂ List.cons NativeShiftTemplateR9Proofs.block
      (congrArg₂ List.cons NativeShiftTemplateR10Proofs.block
      (congrArg₂ List.cons (show dataT37Column2Block156 = (.affine 2047 32 32 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block157 = (.affine 2048 0 32 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block158 = (.affine 2048 0 32 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block159 = (.affine 2048 0 32 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block160 = (.affine 2048 0 32 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block161 = (.affine 2048 0 32 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block162 = (.affine 2048 0 32 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block163 = (.affine 2048 0 32 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block164 = (.affine 2048 0 32 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block165 = (.affine 2048 0 32 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block166 = (.affine 2048 0 32 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block167 = (.affine 2048 0 32 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block168 = (.affine 2048 0 32 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block169 = (.affine 2048 0 32 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block170 = (.affine 2048 0 32 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block171 = (.affine 2048 0 32 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block172 = (.affine 2048 0 32 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block173 = (.affine 2048 0 32 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block174 = (.affine 2048 0 32 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block175 = (.affine 2048 0 32 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block176 = (.affine 2048 0 32 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block177 = (.affine 2048 0 32 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block178 = (.affine 2048 0 32 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block179 = (.affine 2048 0 32 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block180 = (.affine 2048 0 32 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block181 = (.affine 2048 0 32 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block182 = (.affine 2048 0 32 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block183 = (.affine 2048 0 32 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block184 = (.affine 2048 0 32 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block185 = (.affine 2048 0 32 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block186 = (.affine 2048 0 32 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block187 = (.affine 2048 0 32 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block188 = (.affine 4096 0 16 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block189 = (.affine 4096 0 16 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block190 = (.affine 4096 0 16 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block191 = (.affine 4096 0 16 : Block) from rfl)
      (Eq.refl ([] : List Block))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

end Airbender.ReducedMachine.NativeShiftShapeProofs
