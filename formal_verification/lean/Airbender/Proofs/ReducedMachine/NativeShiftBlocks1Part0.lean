import Airbender.Proofs.ReducedMachine.NativeShiftTemplates

namespace Airbender.ReducedMachine.NativeShiftShapeProofs
open Setup Verification NativeFixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

-- Canonical block descriptions from the already certified standalone column shapes.
def column1Part0 : List Block :=
  [.affine 65536 0 1,
   .affine 32768 0 2,
   .affine 32768 0 2,
   .affine 16384 0 4,
   .affine 16384 0 4,
   .affine 16384 0 4,
   .affine 16384 0 4,
   .affine 8192 0 8,
   .affine 8192 0 8,
   .affine 8192 0 8,
   .affine 8192 0 8,
   .affine 8192 0 8,
   .affine 8192 0 8,
   .affine 8192 0 8,
   .affine 8192 0 8,
   .affine 4096 0 16,
   .affine 4096 0 16,
   .affine 4096 0 16,
   .affine 4096 0 16,
   .affine 4096 0 16,
   .affine 4096 0 16,
   .affine 4096 0 16,
   .affine 4096 0 16,
   .affine 4096 0 16,
   .affine 4096 0 16,
   .affine 4096 0 16,
   .affine 4096 0 16,
   .affine 4096 0 16,
   .affine 4096 0 16,
   .affine 4096 0 16,
   .affine 4096 0 16,
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
   .affine 2048 0 32,
   .periodic 64 0 SllHighProofs.template6]

/-- Assemble literal identities without comparing whole imported columns. -/
theorem blocks1Part0 :
    [dataT37Column1Block0,
     dataT37Column1Block1,
     dataT37Column1Block2,
     dataT37Column1Block3,
     dataT37Column1Block4,
     dataT37Column1Block5,
     dataT37Column1Block6,
     dataT37Column1Block7,
     dataT37Column1Block8,
     dataT37Column1Block9,
     dataT37Column1Block10,
     dataT37Column1Block11,
     dataT37Column1Block12,
     dataT37Column1Block13,
     dataT37Column1Block14,
     dataT37Column1Block15,
     dataT37Column1Block16,
     dataT37Column1Block17,
     dataT37Column1Block18,
     dataT37Column1Block19,
     dataT37Column1Block20,
     dataT37Column1Block21,
     dataT37Column1Block22,
     dataT37Column1Block23,
     dataT37Column1Block24,
     dataT37Column1Block25,
     dataT37Column1Block26,
     dataT37Column1Block27,
     dataT37Column1Block28,
     dataT37Column1Block29,
     dataT37Column1Block30,
     dataT37Column1Block31,
     dataT37Column1Block32,
     dataT37Column1Block33,
     dataT37Column1Block34,
     dataT37Column1Block35,
     dataT37Column1Block36,
     dataT37Column1Block37,
     dataT37Column1Block38,
     dataT37Column1Block39,
     dataT37Column1Block40,
     dataT37Column1Block41,
     dataT37Column1Block42,
     dataT37Column1Block43,
     dataT37Column1Block44,
     dataT37Column1Block45,
     dataT37Column1Block46,
     dataT37Column1Block47,
     dataT37Column1Block48,
     dataT37Column1Block49,
     dataT37Column1Block50,
     dataT37Column1Block51,
     dataT37Column1Block52,
     dataT37Column1Block53,
     dataT37Column1Block54,
     dataT37Column1Block55,
     dataT37Column1Block56,
     dataT37Column1Block57,
     dataT37Column1Block58,
     dataT37Column1Block59,
     dataT37Column1Block60,
     dataT37Column1Block61,
     dataT37Column1Block62,
     dataT37Column1Block63] = column1Part0 := by
  exact (congrArg₂ List.cons (show dataT37Column1Block0 = (.affine 65536 0 1 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column1Block1 = (.affine 32768 0 2 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column1Block2 = (.affine 32768 0 2 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column1Block3 = (.affine 16384 0 4 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column1Block4 = (.affine 16384 0 4 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column1Block5 = (.affine 16384 0 4 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column1Block6 = (.affine 16384 0 4 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column1Block7 = (.affine 8192 0 8 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column1Block8 = (.affine 8192 0 8 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column1Block9 = (.affine 8192 0 8 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column1Block10 = (.affine 8192 0 8 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column1Block11 = (.affine 8192 0 8 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column1Block12 = (.affine 8192 0 8 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column1Block13 = (.affine 8192 0 8 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column1Block14 = (.affine 8192 0 8 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column1Block15 = (.affine 4096 0 16 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column1Block16 = (.affine 4096 0 16 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column1Block17 = (.affine 4096 0 16 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column1Block18 = (.affine 4096 0 16 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column1Block19 = (.affine 4096 0 16 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column1Block20 = (.affine 4096 0 16 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column1Block21 = (.affine 4096 0 16 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column1Block22 = (.affine 4096 0 16 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column1Block23 = (.affine 4096 0 16 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column1Block24 = (.affine 4096 0 16 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column1Block25 = (.affine 4096 0 16 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column1Block26 = (.affine 4096 0 16 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column1Block27 = (.affine 4096 0 16 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column1Block28 = (.affine 4096 0 16 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column1Block29 = (.affine 4096 0 16 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column1Block30 = (.affine 4096 0 16 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column1Block31 = (.affine 2048 0 32 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column1Block32 = (.affine 2048 0 32 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column1Block33 = (.affine 2048 0 32 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column1Block34 = (.affine 2048 0 32 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column1Block35 = (.affine 2048 0 32 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column1Block36 = (.affine 2048 0 32 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column1Block37 = (.affine 2048 0 32 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column1Block38 = (.affine 2048 0 32 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column1Block39 = (.affine 2048 0 32 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column1Block40 = (.affine 2048 0 32 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column1Block41 = (.affine 2048 0 32 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column1Block42 = (.affine 2048 0 32 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column1Block43 = (.affine 2048 0 32 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column1Block44 = (.affine 2048 0 32 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column1Block45 = (.affine 2048 0 32 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column1Block46 = (.affine 2048 0 32 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column1Block47 = (.affine 2048 0 32 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column1Block48 = (.affine 2048 0 32 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column1Block49 = (.affine 2048 0 32 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column1Block50 = (.affine 2048 0 32 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column1Block51 = (.affine 2048 0 32 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column1Block52 = (.affine 2048 0 32 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column1Block53 = (.affine 2048 0 32 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column1Block54 = (.affine 2048 0 32 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column1Block55 = (.affine 2048 0 32 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column1Block56 = (.affine 2048 0 32 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column1Block57 = (.affine 2048 0 32 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column1Block58 = (.affine 2048 0 32 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column1Block59 = (.affine 2048 0 32 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column1Block60 = (.affine 2048 0 32 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column1Block61 = (.affine 2048 0 32 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column1Block62 = (.affine 2048 0 32 : Block) from rfl)
      (congrArg₂ List.cons NativeShiftTemplateL6Proofs.block
      (Eq.refl ([] : List Block))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

end Airbender.ReducedMachine.NativeShiftShapeProofs
