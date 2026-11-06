import Airbender.Proofs.ReducedMachine.NativeShiftTemplates

namespace Airbender.ReducedMachine.NativeShiftShapeProofs
open Setup Verification NativeFixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

-- Canonical block descriptions from the already certified standalone column shapes.
def column2Part4 : List Block :=
  [.affine 2048 27 0,
   .affine 2048 28 0,
   .affine 2048 29 0,
   .affine 2048 30 0,
   .affine 2048 31 0,
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
   .affine 32768 1 0]

/-- Assemble literal identities without comparing whole imported columns. -/
theorem blocks2Part4 :
    [dataT37Column2Block256,
     dataT37Column2Block257,
     dataT37Column2Block258,
     dataT37Column2Block259,
     dataT37Column2Block260,
     dataT37Column2Block261,
     dataT37Column2Block262,
     dataT37Column2Block263,
     dataT37Column2Block264,
     dataT37Column2Block265,
     dataT37Column2Block266,
     dataT37Column2Block267,
     dataT37Column2Block268,
     dataT37Column2Block269,
     dataT37Column2Block270,
     dataT37Column2Block271,
     dataT37Column2Block272,
     dataT37Column2Block273,
     dataT37Column2Block274,
     dataT37Column2Block275,
     dataT37Column2Block276,
     dataT37Column2Block277,
     dataT37Column2Block278,
     dataT37Column2Block279,
     dataT37Column2Block280,
     dataT37Column2Block281,
     dataT37Column2Block282,
     dataT37Column2Block283,
     dataT37Column2Block284,
     dataT37Column2Block285,
     dataT37Column2Block286,
     dataT37Column2Block287,
     dataT37Column2Block288,
     dataT37Column2Block289,
     dataT37Column2Block290] = column2Part4 := by
  exact (congrArg₂ List.cons (show dataT37Column2Block256 = (.affine 2048 27 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block257 = (.affine 2048 28 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block258 = (.affine 2048 29 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block259 = (.affine 2048 30 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block260 = (.affine 2048 31 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block261 = (.affine 4096 0 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block262 = (.affine 4096 1 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block263 = (.affine 4096 2 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block264 = (.affine 4096 3 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block265 = (.affine 4096 4 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block266 = (.affine 4096 5 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block267 = (.affine 4096 6 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block268 = (.affine 4096 7 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block269 = (.affine 4096 8 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block270 = (.affine 4096 9 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block271 = (.affine 4096 10 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block272 = (.affine 4096 11 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block273 = (.affine 4096 12 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block274 = (.affine 4096 13 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block275 = (.affine 4096 14 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block276 = (.affine 4096 15 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block277 = (.affine 8192 0 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block278 = (.affine 8192 1 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block279 = (.affine 8192 2 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block280 = (.affine 8192 3 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block281 = (.affine 8192 4 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block282 = (.affine 8192 5 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block283 = (.affine 8192 6 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block284 = (.affine 8192 7 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block285 = (.affine 16384 0 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block286 = (.affine 16384 1 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block287 = (.affine 16384 2 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block288 = (.affine 16384 3 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block289 = (.affine 32768 0 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block290 = (.affine 32768 1 0 : Block) from rfl)
      (Eq.refl ([] : List Block)))))))))))))))))))))))))))))))))))))

end Airbender.ReducedMachine.NativeShiftShapeProofs
