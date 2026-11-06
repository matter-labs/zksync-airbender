import Airbender.Proofs.ReducedMachine.NativeShiftTemplates

namespace Airbender.ReducedMachine.NativeShiftShapeProofs
open Setup Verification NativeFixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

-- Canonical block descriptions from the already certified standalone column shapes.
def column1Part1 : List Block :=
  [.periodic 128 0 SllHighProofs.template7,
   .periodic 256 0 SllHighProofs.template8,
   .periodic 512 0 SllHighProofs.template9,
   .periodic 1024 0 SllHighProofs.template10,
   .periodic 2048 0 SllHighProofs.template11,
   .periodic 4096 0 SllHighProofs.template12,
   .periodic 8192 0 SllHighProofs.template13,
   .periodic 16384 0 SllHighProofs.template14,
   .periodic 32768 0 SllHighProofs.template15,
   .affine 1048577 0 0,
   .affine 65535 1 1,
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
   .affine 2048 26 0,
   .affine 2048 27 0,
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
   .affine 4096 10 0]

/-- Assemble literal identities without comparing whole imported columns. -/
theorem blocks1Part1 :
    [dataT37Column1Block64,
     dataT37Column1Block65,
     dataT37Column1Block66,
     dataT37Column1Block67,
     dataT37Column1Block68,
     dataT37Column1Block69,
     dataT37Column1Block70,
     dataT37Column1Block71,
     dataT37Column1Block72,
     dataT37Column1Block73,
     dataT37Column1Block74,
     dataT37Column1Block75,
     dataT37Column1Block76,
     dataT37Column1Block77,
     dataT37Column1Block78,
     dataT37Column1Block79,
     dataT37Column1Block80,
     dataT37Column1Block81,
     dataT37Column1Block82,
     dataT37Column1Block83,
     dataT37Column1Block84,
     dataT37Column1Block85,
     dataT37Column1Block86,
     dataT37Column1Block87,
     dataT37Column1Block88,
     dataT37Column1Block89,
     dataT37Column1Block90,
     dataT37Column1Block91,
     dataT37Column1Block92,
     dataT37Column1Block93,
     dataT37Column1Block94,
     dataT37Column1Block95,
     dataT37Column1Block96,
     dataT37Column1Block97,
     dataT37Column1Block98,
     dataT37Column1Block99,
     dataT37Column1Block100,
     dataT37Column1Block101,
     dataT37Column1Block102,
     dataT37Column1Block103,
     dataT37Column1Block104,
     dataT37Column1Block105,
     dataT37Column1Block106,
     dataT37Column1Block107,
     dataT37Column1Block108,
     dataT37Column1Block109,
     dataT37Column1Block110,
     dataT37Column1Block111,
     dataT37Column1Block112,
     dataT37Column1Block113,
     dataT37Column1Block114,
     dataT37Column1Block115,
     dataT37Column1Block116,
     dataT37Column1Block117,
     dataT37Column1Block118,
     dataT37Column1Block119,
     dataT37Column1Block120,
     dataT37Column1Block121,
     dataT37Column1Block122,
     dataT37Column1Block123,
     dataT37Column1Block124,
     dataT37Column1Block125,
     dataT37Column1Block126,
     dataT37Column1Block127] = column1Part1 := by
  exact (congrArg₂ List.cons NativeShiftTemplateL7Proofs.block
      (congrArg₂ List.cons NativeShiftTemplateL8Proofs.block
      (congrArg₂ List.cons NativeShiftTemplateL9Proofs.block
      (congrArg₂ List.cons NativeShiftTemplateL10Proofs.block
      (congrArg₂ List.cons NativeShiftTemplateL11Proofs.block
      (congrArg₂ List.cons NativeShiftTemplateL12Proofs.block
      (congrArg₂ List.cons NativeShiftTemplateL13Proofs.block
      (congrArg₂ List.cons NativeShiftTemplateL14Proofs.block
      (congrArg₂ List.cons NativeShiftTemplateL15Proofs.block
      (congrArg₂ List.cons (show dataT37Column1Block73 = (.affine 1048577 0 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column1Block74 = (.affine 65535 1 1 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column1Block75 = (.periodic 32768 1 (Array.replicate 2 0) : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column1Block76 = (.periodic 16384 1 (Array.replicate 4 0) : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column1Block77 = (.periodic 8192 1 (Array.replicate 8 0) : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column1Block78 = (.periodic 4096 1 (Array.replicate 16 0) : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column1Block79 = (.periodic 2048 1 (Array.replicate 32 0) : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column1Block80 = (.periodic 1024 1 (Array.replicate 64 0) : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column1Block81 = (.periodic 512 1 (Array.replicate 128 0) : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column1Block82 = (.periodic 256 1 (Array.replicate 256 0) : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column1Block83 = (.periodic 128 1 (Array.replicate 512 0) : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column1Block84 = (.periodic 64 1 (Array.replicate 1024 0) : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column1Block85 = (.affine 2048 0 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column1Block86 = (.affine 2048 1 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column1Block87 = (.affine 2048 2 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column1Block88 = (.affine 2048 3 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column1Block89 = (.affine 2048 4 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column1Block90 = (.affine 2048 5 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column1Block91 = (.affine 2048 6 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column1Block92 = (.affine 2048 7 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column1Block93 = (.affine 2048 8 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column1Block94 = (.affine 2048 9 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column1Block95 = (.affine 2048 10 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column1Block96 = (.affine 2048 11 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column1Block97 = (.affine 2048 12 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column1Block98 = (.affine 2048 13 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column1Block99 = (.affine 2048 14 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column1Block100 = (.affine 2048 15 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column1Block101 = (.affine 2048 16 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column1Block102 = (.affine 2048 17 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column1Block103 = (.affine 2048 18 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column1Block104 = (.affine 2048 19 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column1Block105 = (.affine 2048 20 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column1Block106 = (.affine 2048 21 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column1Block107 = (.affine 2048 22 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column1Block108 = (.affine 2048 23 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column1Block109 = (.affine 2048 24 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column1Block110 = (.affine 2048 25 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column1Block111 = (.affine 2048 26 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column1Block112 = (.affine 2048 27 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column1Block113 = (.affine 2048 28 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column1Block114 = (.affine 2048 29 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column1Block115 = (.affine 2048 30 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column1Block116 = (.affine 2048 31 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column1Block117 = (.affine 4096 0 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column1Block118 = (.affine 4096 1 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column1Block119 = (.affine 4096 2 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column1Block120 = (.affine 4096 3 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column1Block121 = (.affine 4096 4 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column1Block122 = (.affine 4096 5 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column1Block123 = (.affine 4096 6 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column1Block124 = (.affine 4096 7 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column1Block125 = (.affine 4096 8 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column1Block126 = (.affine 4096 9 0 : Block) from rfl)
      (congrArg₂ List.cons (show dataT37Column1Block127 = (.affine 4096 10 0 : Block) from rfl)
      (Eq.refl ([] : List Block))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

end Airbender.ReducedMachine.NativeShiftShapeProofs
