import Airbender.Proofs.ReducedMachine.NativeShiftTemplates

namespace Airbender.ReducedMachine.NativeShiftShapeProofs
open Setup Verification NativeFixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

-- Canonical block descriptions from the already certified standalone column shapes.
def column2Part1 : List Block :=
  [.periodic 256 1 (Array.replicate 256 0),
   .periodic 512 1 (Array.replicate 128 0),
   .periodic 1024 1 (Array.replicate 64 0),
   .periodic 2048 1 (Array.replicate 32 0),
   .periodic 4096 1 (Array.replicate 16 0),
   .periodic 8192 1 (Array.replicate 8 0),
   .periodic 16384 1 (Array.replicate 4 0),
   .periodic 32768 1 (Array.replicate 2 0),
   .affine 65536 0 1,
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
   .affine 2048 0 32]

/-- Assemble literal identities without comparing whole imported columns. -/
theorem blocks2Part1 :
    [dataT37Column2Block64,
     dataT37Column2Block65,
     dataT37Column2Block66,
     dataT37Column2Block67,
     dataT37Column2Block68,
     dataT37Column2Block69,
     dataT37Column2Block70,
     dataT37Column2Block71,
     dataT37Column2Block72,
     dataT37Column2Block73,
     dataT37Column2Block74,
     dataT37Column2Block75,
     dataT37Column2Block76,
     dataT37Column2Block77,
     dataT37Column2Block78,
     dataT37Column2Block79,
     dataT37Column2Block80,
     dataT37Column2Block81,
     dataT37Column2Block82,
     dataT37Column2Block83,
     dataT37Column2Block84,
     dataT37Column2Block85,
     dataT37Column2Block86,
     dataT37Column2Block87,
     dataT37Column2Block88,
     dataT37Column2Block89,
     dataT37Column2Block90,
     dataT37Column2Block91,
     dataT37Column2Block92,
     dataT37Column2Block93,
     dataT37Column2Block94,
     dataT37Column2Block95,
     dataT37Column2Block96,
     dataT37Column2Block97,
     dataT37Column2Block98,
     dataT37Column2Block99,
     dataT37Column2Block100,
     dataT37Column2Block101,
     dataT37Column2Block102,
     dataT37Column2Block103,
     dataT37Column2Block104,
     dataT37Column2Block105,
     dataT37Column2Block106,
     dataT37Column2Block107,
     dataT37Column2Block108,
     dataT37Column2Block109,
     dataT37Column2Block110,
     dataT37Column2Block111,
     dataT37Column2Block112,
     dataT37Column2Block113,
     dataT37Column2Block114,
     dataT37Column2Block115,
     dataT37Column2Block116,
     dataT37Column2Block117,
     dataT37Column2Block118,
     dataT37Column2Block119,
     dataT37Column2Block120,
     dataT37Column2Block121,
     dataT37Column2Block122,
     dataT37Column2Block123,
     dataT37Column2Block124,
     dataT37Column2Block125,
     dataT37Column2Block126,
     dataT37Column2Block127] = column2Part1 := by
  exact (congrArg₂ List.cons (show dataT37Column2Block64 = (.periodic 256 1 (Array.replicate 256 0) : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block65 = (.periodic 512 1 (Array.replicate 128 0) : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block66 = (.periodic 1024 1 (Array.replicate 64 0) : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block67 = (.periodic 2048 1 (Array.replicate 32 0) : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block68 = (.periodic 4096 1 (Array.replicate 16 0) : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block69 = (.periodic 8192 1 (Array.replicate 8 0) : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block70 = (.periodic 16384 1 (Array.replicate 4 0) : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block71 = (.periodic 32768 1 (Array.replicate 2 0) : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block72 = (.affine 65536 0 1 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block73 = (.affine 32768 0 2 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block74 = (.affine 32768 0 2 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block75 = (.affine 16384 0 4 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block76 = (.affine 16384 0 4 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block77 = (.affine 16384 0 4 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block78 = (.affine 16384 0 4 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block79 = (.affine 8192 0 8 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block80 = (.affine 8192 0 8 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block81 = (.affine 8192 0 8 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block82 = (.affine 8192 0 8 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block83 = (.affine 8192 0 8 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block84 = (.affine 8192 0 8 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block85 = (.affine 8192 0 8 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block86 = (.affine 8192 0 8 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block87 = (.affine 4096 0 16 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block88 = (.affine 4096 0 16 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block89 = (.affine 4096 0 16 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block90 = (.affine 4096 0 16 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block91 = (.affine 4096 0 16 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block92 = (.affine 4096 0 16 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block93 = (.affine 4096 0 16 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block94 = (.affine 4096 0 16 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block95 = (.affine 4096 0 16 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block96 = (.affine 4096 0 16 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block97 = (.affine 4096 0 16 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block98 = (.affine 4096 0 16 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block99 = (.affine 4096 0 16 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block100 = (.affine 4096 0 16 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block101 = (.affine 4096 0 16 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block102 = (.affine 4096 0 16 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block103 = (.affine 2048 0 32 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block104 = (.affine 2048 0 32 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block105 = (.affine 2048 0 32 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block106 = (.affine 2048 0 32 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block107 = (.affine 2048 0 32 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block108 = (.affine 2048 0 32 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block109 = (.affine 2048 0 32 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block110 = (.affine 2048 0 32 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block111 = (.affine 2048 0 32 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block112 = (.affine 2048 0 32 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block113 = (.affine 2048 0 32 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block114 = (.affine 2048 0 32 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block115 = (.affine 2048 0 32 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block116 = (.affine 2048 0 32 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block117 = (.affine 2048 0 32 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block118 = (.affine 2048 0 32 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block119 = (.affine 2048 0 32 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block120 = (.affine 2048 0 32 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block121 = (.affine 2048 0 32 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block122 = (.affine 2048 0 32 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block123 = (.affine 2048 0 32 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block124 = (.affine 2048 0 32 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block125 = (.affine 2048 0 32 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block126 = (.affine 2048 0 32 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column2Block127 = (.affine 2048 0 32 : Block) from rfl)
      (Eq.refl ([] : List Block))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

end Airbender.ReducedMachine.NativeShiftShapeProofs
