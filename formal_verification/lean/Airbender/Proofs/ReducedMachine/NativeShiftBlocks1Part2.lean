import Airbender.Proofs.ReducedMachine.NativeShiftTemplates

namespace Airbender.ReducedMachine.NativeShiftShapeProofs
open Setup Verification NativeFixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

-- Canonical block descriptions from the already certified standalone column shapes.
def column1Part2 : List Block :=
  [.affine 4096 11 0,
   .affine 4096 12 0,
   .affine 4096 13 0,
   .affine 4096 14 0,
   .affine 4096 15 0,
   .affine 8192 0 0,
   .affine 8192 1 0,
   .affine 8192 2 0,
   .affine 8192 3 0,
   .affine 8192 4 0,
   .affine 8192 5 0,
   .affine 8192 6 0,
   .affine 8192 7 0,
   .affine 16384 0 0,
   .affine 16384 1 0,
   .affine 16384 2 0,
   .affine 16384 3 0,
   .affine 32768 0 0,
   .affine 32768 1 0,
   .affine 1048576 0 0]

/-- Assemble literal identities without comparing whole imported columns. -/
theorem blocks1Part2 :
    [dataT37Column1Block128,
     dataT37Column1Block129,
     dataT37Column1Block130,
     dataT37Column1Block131,
     dataT37Column1Block132,
     dataT37Column1Block133,
     dataT37Column1Block134,
     dataT37Column1Block135,
     dataT37Column1Block136,
     dataT37Column1Block137,
     dataT37Column1Block138,
     dataT37Column1Block139,
     dataT37Column1Block140,
     dataT37Column1Block141,
     dataT37Column1Block142,
     dataT37Column1Block143,
     dataT37Column1Block144,
     dataT37Column1Block145,
     dataT37Column1Block146,
     dataT37Column1Block147] = column1Part2 := by
  exact (congrArg₂ List.cons (show dataT37Column1Block128 = (.affine 4096 11 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column1Block129 = (.affine 4096 12 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column1Block130 = (.affine 4096 13 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column1Block131 = (.affine 4096 14 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column1Block132 = (.affine 4096 15 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column1Block133 = (.affine 8192 0 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column1Block134 = (.affine 8192 1 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column1Block135 = (.affine 8192 2 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column1Block136 = (.affine 8192 3 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column1Block137 = (.affine 8192 4 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column1Block138 = (.affine 8192 5 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column1Block139 = (.affine 8192 6 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column1Block140 = (.affine 8192 7 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column1Block141 = (.affine 16384 0 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column1Block142 = (.affine 16384 1 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column1Block143 = (.affine 16384 2 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column1Block144 = (.affine 16384 3 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column1Block145 = (.affine 32768 0 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column1Block146 = (.affine 32768 1 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column1Block147 = (.affine 1048576 0 0 : Block) from rfl)
      (Eq.refl ([] : List Block))))))))))))))))))))))

end Airbender.ReducedMachine.NativeShiftShapeProofs
