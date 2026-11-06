import Airbender.Proofs.ReducedMachine.NativeShiftTemplates

namespace Airbender.ReducedMachine.NativeShiftShapeProofs
open Setup Verification NativeFixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

-- Canonical block descriptions from the already certified standalone column shapes.
def column2Part3 : List Block :=
  [.affine 4096 0 16,
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
   .affine 8192 0 8,
   .affine 8192 0 8,
   .affine 8192 0 8,
   .affine 8192 0 8,
   .affine 8192 0 8,
   .affine 8192 0 8,
   .affine 8192 0 8,
   .affine 8192 0 8,
   .affine 16384 0 4,
   .affine 16384 0 4,
   .affine 16384 0 4,
   .affine 16384 0 4,
   .affine 32768 0 2,
   .affine 32768 0 2,
   .affine 65536 0 1,
   .periodic 32768 1 (Array.replicate 2 0),
   .periodic 16384 1 (Array.replicate 4 0),
   .periodic 8192 1 (Array.replicate 8 0),
   .periodic 4096 1 (Array.replicate 16 0),
   .periodic 2048 1 (Array.replicate 32 0),
   .periodic 1024 1 (Array.replicate 64 0),
   .periodic 512 1 (Array.replicate 128 0),
   .periodic 256 1 (Array.replicate 256 0),
   .periodic 128 1 (Array.replicate 512 0),
   .periodic 64 1 (Array.replicate 1024 0),
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
   .affine 2048 26 0]

/-- Assemble literal identities without comparing whole imported columns. -/
theorem blocks2Part3 :
    [dataT37Column2Block192,
     dataT37Column2Block193,
     dataT37Column2Block194,
     dataT37Column2Block195,
     dataT37Column2Block196,
     dataT37Column2Block197,
     dataT37Column2Block198,
     dataT37Column2Block199,
     dataT37Column2Block200,
     dataT37Column2Block201,
     dataT37Column2Block202,
     dataT37Column2Block203,
     dataT37Column2Block204,
     dataT37Column2Block205,
     dataT37Column2Block206,
     dataT37Column2Block207,
     dataT37Column2Block208,
     dataT37Column2Block209,
     dataT37Column2Block210,
     dataT37Column2Block211,
     dataT37Column2Block212,
     dataT37Column2Block213,
     dataT37Column2Block214,
     dataT37Column2Block215,
     dataT37Column2Block216,
     dataT37Column2Block217,
     dataT37Column2Block218,
     dataT37Column2Block219,
     dataT37Column2Block220,
     dataT37Column2Block221,
     dataT37Column2Block222,
     dataT37Column2Block223,
     dataT37Column2Block224,
     dataT37Column2Block225,
     dataT37Column2Block226,
     dataT37Column2Block227,
     dataT37Column2Block228,
     dataT37Column2Block229,
     dataT37Column2Block230,
     dataT37Column2Block231,
     dataT37Column2Block232,
     dataT37Column2Block233,
     dataT37Column2Block234,
     dataT37Column2Block235,
     dataT37Column2Block236,
     dataT37Column2Block237,
     dataT37Column2Block238,
     dataT37Column2Block239,
     dataT37Column2Block240,
     dataT37Column2Block241,
     dataT37Column2Block242,
     dataT37Column2Block243,
     dataT37Column2Block244,
     dataT37Column2Block245,
     dataT37Column2Block246,
     dataT37Column2Block247,
     dataT37Column2Block248,
     dataT37Column2Block249,
     dataT37Column2Block250,
     dataT37Column2Block251,
     dataT37Column2Block252,
     dataT37Column2Block253,
     dataT37Column2Block254,
     dataT37Column2Block255] = column2Part3 := by
  exact (congrArg₂ List.cons (show dataT37Column2Block192 = (.affine 4096 0 16 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block193 = (.affine 4096 0 16 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block194 = (.affine 4096 0 16 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block195 = (.affine 4096 0 16 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block196 = (.affine 4096 0 16 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block197 = (.affine 4096 0 16 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block198 = (.affine 4096 0 16 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block199 = (.affine 4096 0 16 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block200 = (.affine 4096 0 16 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block201 = (.affine 4096 0 16 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block202 = (.affine 4096 0 16 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block203 = (.affine 4096 0 16 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block204 = (.affine 8192 0 8 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block205 = (.affine 8192 0 8 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block206 = (.affine 8192 0 8 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block207 = (.affine 8192 0 8 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block208 = (.affine 8192 0 8 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block209 = (.affine 8192 0 8 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block210 = (.affine 8192 0 8 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block211 = (.affine 8192 0 8 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block212 = (.affine 16384 0 4 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block213 = (.affine 16384 0 4 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block214 = (.affine 16384 0 4 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block215 = (.affine 16384 0 4 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block216 = (.affine 32768 0 2 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block217 = (.affine 32768 0 2 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block218 = (.affine 65536 0 1 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block219 = (.periodic 32768 1 (Array.replicate 2 0) : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block220 = (.periodic 16384 1 (Array.replicate 4 0) : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block221 = (.periodic 8192 1 (Array.replicate 8 0) : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block222 = (.periodic 4096 1 (Array.replicate 16 0) : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block223 = (.periodic 2048 1 (Array.replicate 32 0) : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block224 = (.periodic 1024 1 (Array.replicate 64 0) : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block225 = (.periodic 512 1 (Array.replicate 128 0) : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block226 = (.periodic 256 1 (Array.replicate 256 0) : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block227 = (.periodic 128 1 (Array.replicate 512 0) : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block228 = (.periodic 64 1 (Array.replicate 1024 0) : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block229 = (.affine 2048 0 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block230 = (.affine 2048 1 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block231 = (.affine 2048 2 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block232 = (.affine 2048 3 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block233 = (.affine 2048 4 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block234 = (.affine 2048 5 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block235 = (.affine 2048 6 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block236 = (.affine 2048 7 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block237 = (.affine 2048 8 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block238 = (.affine 2048 9 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block239 = (.affine 2048 10 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block240 = (.affine 2048 11 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block241 = (.affine 2048 12 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block242 = (.affine 2048 13 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block243 = (.affine 2048 14 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block244 = (.affine 2048 15 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block245 = (.affine 2048 16 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block246 = (.affine 2048 17 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block247 = (.affine 2048 18 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block248 = (.affine 2048 19 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block249 = (.affine 2048 20 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block250 = (.affine 2048 21 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block251 = (.affine 2048 22 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block252 = (.affine 2048 23 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block253 = (.affine 2048 24 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block254 = (.affine 2048 25 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block255 = (.affine 2048 26 0 : Block) from rfl)
      (Eq.refl ([] : List Block))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

end Airbender.ReducedMachine.NativeShiftShapeProofs
