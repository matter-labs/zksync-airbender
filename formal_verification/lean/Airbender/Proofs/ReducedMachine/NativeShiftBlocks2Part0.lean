import Airbender.Proofs.ReducedMachine.NativeShiftTemplates

namespace Airbender.ReducedMachine.NativeShiftShapeProofs
open Setup Verification NativeFixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

-- Canonical block descriptions from the already certified standalone column shapes.
def column2Part0 : List Block :=
  [.affine 98304 0 0,
   .affine 32768 1 0,
   .affine 16384 0 0,
   .affine 16384 1 0,
   .affine 16384 2 0,
   .affine 16384 3 0,
   .affine 8192 0 0,
   .affine 8192 1 0,
   .affine 8192 2 0,
   .affine 8192 3 0,
   .affine 8192 4 0,
   .affine 8192 5 0,
   .affine 8192 6 0,
   .affine 8192 7 0,
   .affine 4096 0 0,
   .affine 4096 1 0,
   .affine 4096 2 0,
   .affine 4096 3 0,
   .affine 4096 4 0,
   .affine 4096 5 0,
   .affine 4096 6 0,
   .affine 4096 7 0,
   .affine 4096 8 0,
   .affine 4096 9 0,
   .affine 4096 10 0,
   .affine 4096 11 0,
   .affine 4096 12 0,
   .affine 4096 13 0,
   .affine 4096 14 0,
   .affine 4096 15 0,
   .affine 2048 0 0,
   .affine 2048 1 0,
   .affine 2048 2 0,
   .affine 2048 3 0,
   .affine 2048 4 0,
   .affine 2048 5 0,
   .affine 2048 6 0,
   .affine 2048 7 0,
   .affine 2048 8 0,
   .affine 2048 9 0,
   .affine 2048 10 0,
   .affine 2048 11 0,
   .affine 2048 12 0,
   .affine 2048 13 0,
   .affine 2048 14 0,
   .affine 2048 15 0,
   .affine 2048 16 0,
   .affine 2048 17 0,
   .affine 2048 18 0,
   .affine 2048 19 0,
   .affine 2048 20 0,
   .affine 2048 21 0,
   .affine 2048 22 0,
   .affine 2048 23 0,
   .affine 2048 24 0,
   .affine 2048 25 0,
   .affine 2048 26 0,
   .affine 2048 27 0,
   .affine 2048 28 0,
   .affine 2048 29 0,
   .affine 2048 30 0,
   .affine 2048 31 0,
   .periodic 64 1 (Array.replicate 1024 0),
   .periodic 128 1 (Array.replicate 512 0)]

/-- Assemble literal identities without comparing whole imported columns. -/
theorem blocks2Part0 :
    [dataT37Column2Block0,
     dataT37Column2Block1,
     dataT37Column2Block2,
     dataT37Column2Block3,
     dataT37Column2Block4,
     dataT37Column2Block5,
     dataT37Column2Block6,
     dataT37Column2Block7,
     dataT37Column2Block8,
     dataT37Column2Block9,
     dataT37Column2Block10,
     dataT37Column2Block11,
     dataT37Column2Block12,
     dataT37Column2Block13,
     dataT37Column2Block14,
     dataT37Column2Block15,
     dataT37Column2Block16,
     dataT37Column2Block17,
     dataT37Column2Block18,
     dataT37Column2Block19,
     dataT37Column2Block20,
     dataT37Column2Block21,
     dataT37Column2Block22,
     dataT37Column2Block23,
     dataT37Column2Block24,
     dataT37Column2Block25,
     dataT37Column2Block26,
     dataT37Column2Block27,
     dataT37Column2Block28,
     dataT37Column2Block29,
     dataT37Column2Block30,
     dataT37Column2Block31,
     dataT37Column2Block32,
     dataT37Column2Block33,
     dataT37Column2Block34,
     dataT37Column2Block35,
     dataT37Column2Block36,
     dataT37Column2Block37,
     dataT37Column2Block38,
     dataT37Column2Block39,
     dataT37Column2Block40,
     dataT37Column2Block41,
     dataT37Column2Block42,
     dataT37Column2Block43,
     dataT37Column2Block44,
     dataT37Column2Block45,
     dataT37Column2Block46,
     dataT37Column2Block47,
     dataT37Column2Block48,
     dataT37Column2Block49,
     dataT37Column2Block50,
     dataT37Column2Block51,
     dataT37Column2Block52,
     dataT37Column2Block53,
     dataT37Column2Block54,
     dataT37Column2Block55,
     dataT37Column2Block56,
     dataT37Column2Block57,
     dataT37Column2Block58,
     dataT37Column2Block59,
     dataT37Column2Block60,
     dataT37Column2Block61,
     dataT37Column2Block62,
     dataT37Column2Block63] = column2Part0 := by
  exact (congrArg₂ List.cons (show dataT37Column2Block0 = (.affine 98304 0 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block1 = (.affine 32768 1 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block2 = (.affine 16384 0 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block3 = (.affine 16384 1 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block4 = (.affine 16384 2 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block5 = (.affine 16384 3 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block6 = (.affine 8192 0 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block7 = (.affine 8192 1 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block8 = (.affine 8192 2 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block9 = (.affine 8192 3 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block10 = (.affine 8192 4 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block11 = (.affine 8192 5 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block12 = (.affine 8192 6 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block13 = (.affine 8192 7 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block14 = (.affine 4096 0 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block15 = (.affine 4096 1 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block16 = (.affine 4096 2 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block17 = (.affine 4096 3 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block18 = (.affine 4096 4 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block19 = (.affine 4096 5 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block20 = (.affine 4096 6 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block21 = (.affine 4096 7 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block22 = (.affine 4096 8 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block23 = (.affine 4096 9 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block24 = (.affine 4096 10 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block25 = (.affine 4096 11 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block26 = (.affine 4096 12 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block27 = (.affine 4096 13 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block28 = (.affine 4096 14 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block29 = (.affine 4096 15 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block30 = (.affine 2048 0 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block31 = (.affine 2048 1 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block32 = (.affine 2048 2 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block33 = (.affine 2048 3 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block34 = (.affine 2048 4 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block35 = (.affine 2048 5 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block36 = (.affine 2048 6 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block37 = (.affine 2048 7 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block38 = (.affine 2048 8 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block39 = (.affine 2048 9 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block40 = (.affine 2048 10 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block41 = (.affine 2048 11 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block42 = (.affine 2048 12 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block43 = (.affine 2048 13 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block44 = (.affine 2048 14 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block45 = (.affine 2048 15 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block46 = (.affine 2048 16 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block47 = (.affine 2048 17 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block48 = (.affine 2048 18 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block49 = (.affine 2048 19 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block50 = (.affine 2048 20 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block51 = (.affine 2048 21 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block52 = (.affine 2048 22 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block53 = (.affine 2048 23 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block54 = (.affine 2048 24 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block55 = (.affine 2048 25 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block56 = (.affine 2048 26 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block57 = (.affine 2048 27 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block58 = (.affine 2048 28 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block59 = (.affine 2048 29 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block60 = (.affine 2048 30 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block61 = (.affine 2048 31 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block62 = (.periodic 64 1 (Array.replicate 1024 0) : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block63 = (.periodic 128 1 (Array.replicate 512 0) : Block) from rfl)
      (Eq.refl ([] : List Block))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

end Airbender.ReducedMachine.NativeShiftShapeProofs
