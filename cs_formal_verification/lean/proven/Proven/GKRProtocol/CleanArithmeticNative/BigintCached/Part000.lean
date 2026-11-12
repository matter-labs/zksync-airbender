module
public import Proven.KernelRfl
import all Mathlib.Data.List.Sort
public import Proven.Import.GKRProtocol.CleanArithmeticImport
public import Proven.GKRProtocol.CleanIdealNative.BigintCached
public import Proven.GKRProtocol.FullArithmeticNative.BigintCached
public import Proven.GKRProtocol.CleanPlacementNative.BigintCached

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.CleanArithmeticNative.BigintCached
open Airbender Airbender.Compiler
set_option maxRecDepth 32768

local instance generatedBatch0Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch0Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

noncomputable def native.relations : List (Polynomial 323 Source.BaseField) :=
  (Airbender.Compiler.FullArithmeticNative.BigintCached.native.artifact).gates.map ArithmeticGate.inputResidual

def native.placementKeys : List Nat :=
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31,
    32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60,
    61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89,
    90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114,
    115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137,
    138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160,
    161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183,
    184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206,
    207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229,
    230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252,
    253, 254, 255, 256, 257, 258, 259, 260, 261, 262, 263, 264, 265, 266, 267, 268, 269, 270, 271, 272, 273, 274, 275]

def native.placementAddresses : List GKRAddress :=
  [GKRAddress.BaseLayerMemory 94, GKRAddress.BaseLayerMemory 95, GKRAddress.BaseLayerMemory 96,
    GKRAddress.BaseLayerMemory 2, GKRAddress.BaseLayerMemory 3, GKRAddress.BaseLayerMemory 6,
    GKRAddress.BaseLayerMemory 7, GKRAddress.BaseLayerMemory 8, GKRAddress.BaseLayerMemory 9,
    GKRAddress.BaseLayerMemory 12, GKRAddress.BaseLayerMemory 13, GKRAddress.BaseLayerMemory 14,
    GKRAddress.BaseLayerMemory 15, GKRAddress.BaseLayerMemory 18, GKRAddress.BaseLayerMemory 19,
    GKRAddress.BaseLayerMemory 20, GKRAddress.BaseLayerMemory 21, GKRAddress.BaseLayerMemory 24,
    GKRAddress.BaseLayerMemory 25, GKRAddress.BaseLayerMemory 26, GKRAddress.BaseLayerMemory 27,
    GKRAddress.BaseLayerMemory 30, GKRAddress.BaseLayerMemory 31, GKRAddress.BaseLayerMemory 32,
    GKRAddress.BaseLayerMemory 33, GKRAddress.BaseLayerMemory 36, GKRAddress.BaseLayerMemory 37,
    GKRAddress.BaseLayerMemory 38, GKRAddress.BaseLayerMemory 39, GKRAddress.BaseLayerMemory 42,
    GKRAddress.BaseLayerMemory 43, GKRAddress.BaseLayerMemory 44, GKRAddress.BaseLayerMemory 45,
    GKRAddress.BaseLayerMemory 48, GKRAddress.BaseLayerMemory 49, GKRAddress.BaseLayerMemory 50,
    GKRAddress.BaseLayerMemory 51, GKRAddress.BaseLayerMemory 54, GKRAddress.BaseLayerMemory 55,
    GKRAddress.BaseLayerMemory 58, GKRAddress.BaseLayerMemory 59, GKRAddress.BaseLayerMemory 62,
    GKRAddress.BaseLayerMemory 63, GKRAddress.BaseLayerMemory 66, GKRAddress.BaseLayerMemory 67,
    GKRAddress.BaseLayerMemory 70, GKRAddress.BaseLayerMemory 71, GKRAddress.BaseLayerMemory 74,
    GKRAddress.BaseLayerMemory 75, GKRAddress.BaseLayerMemory 78, GKRAddress.BaseLayerMemory 79,
    GKRAddress.BaseLayerMemory 82, GKRAddress.BaseLayerMemory 83, GKRAddress.BaseLayerMemory 86,
    GKRAddress.BaseLayerMemory 87, GKRAddress.BaseLayerMemory 90, GKRAddress.BaseLayerMemory 91,
    GKRAddress.BaseLayerMemory 92, GKRAddress.BaseLayerMemory 93, GKRAddress.BaseLayerWitness 0,
    GKRAddress.BaseLayerWitness 1, GKRAddress.BaseLayerWitness 2, GKRAddress.BaseLayerWitness 3,
    GKRAddress.BaseLayerWitness 4, GKRAddress.BaseLayerWitness 5, GKRAddress.BaseLayerWitness 6,
    GKRAddress.BaseLayerWitness 7, GKRAddress.BaseLayerWitness 8, GKRAddress.BaseLayerWitness 9,
    GKRAddress.BaseLayerWitness 10, GKRAddress.BaseLayerWitness 11, GKRAddress.BaseLayerWitness 12,
    GKRAddress.BaseLayerWitness 13, GKRAddress.BaseLayerWitness 14, GKRAddress.BaseLayerWitness 15,
    GKRAddress.BaseLayerWitness 16, GKRAddress.BaseLayerWitness 17, GKRAddress.BaseLayerWitness 18,
    GKRAddress.BaseLayerWitness 19, GKRAddress.BaseLayerWitness 20, GKRAddress.BaseLayerWitness 21,
    GKRAddress.BaseLayerWitness 22, GKRAddress.BaseLayerWitness 23, GKRAddress.BaseLayerWitness 24,
    GKRAddress.BaseLayerWitness 25, GKRAddress.BaseLayerWitness 26, GKRAddress.BaseLayerWitness 27,
    GKRAddress.BaseLayerWitness 28, GKRAddress.BaseLayerWitness 29, GKRAddress.BaseLayerWitness 30,
    GKRAddress.BaseLayerWitness 31, GKRAddress.BaseLayerWitness 32, GKRAddress.BaseLayerWitness 33,
    GKRAddress.BaseLayerWitness 34, GKRAddress.BaseLayerWitness 35, GKRAddress.BaseLayerWitness 36,
    GKRAddress.BaseLayerWitness 37, GKRAddress.BaseLayerWitness 38, GKRAddress.BaseLayerWitness 39,
    GKRAddress.BaseLayerWitness 40, GKRAddress.BaseLayerWitness 41, GKRAddress.BaseLayerWitness 42,
    GKRAddress.BaseLayerWitness 43, GKRAddress.BaseLayerWitness 44, GKRAddress.BaseLayerWitness 45,
    GKRAddress.BaseLayerWitness 46, GKRAddress.BaseLayerWitness 47, GKRAddress.BaseLayerWitness 48,
    GKRAddress.BaseLayerWitness 49, GKRAddress.BaseLayerWitness 50, GKRAddress.BaseLayerWitness 51,
    GKRAddress.BaseLayerWitness 52, GKRAddress.BaseLayerWitness 53, GKRAddress.BaseLayerWitness 54,
    GKRAddress.BaseLayerWitness 55, GKRAddress.BaseLayerWitness 56, GKRAddress.BaseLayerWitness 57,
    GKRAddress.BaseLayerWitness 58, GKRAddress.BaseLayerWitness 59, GKRAddress.BaseLayerWitness 60,
    GKRAddress.BaseLayerWitness 61, GKRAddress.BaseLayerWitness 62, GKRAddress.BaseLayerWitness 63,
    GKRAddress.BaseLayerWitness 64, GKRAddress.BaseLayerWitness 65, GKRAddress.BaseLayerWitness 66,
    GKRAddress.BaseLayerWitness 67, GKRAddress.BaseLayerWitness 68, GKRAddress.BaseLayerWitness 69,
    GKRAddress.BaseLayerWitness 70, GKRAddress.BaseLayerWitness 71, GKRAddress.BaseLayerWitness 72,
    GKRAddress.BaseLayerWitness 73, GKRAddress.BaseLayerWitness 74, GKRAddress.BaseLayerWitness 75,
    GKRAddress.BaseLayerWitness 76, GKRAddress.BaseLayerWitness 77, GKRAddress.BaseLayerWitness 78,
    GKRAddress.BaseLayerWitness 79, GKRAddress.BaseLayerWitness 80, GKRAddress.BaseLayerWitness 81,
    GKRAddress.BaseLayerWitness 82, GKRAddress.BaseLayerWitness 83, GKRAddress.BaseLayerWitness 84,
    GKRAddress.BaseLayerWitness 85, GKRAddress.BaseLayerWitness 86, GKRAddress.BaseLayerWitness 87,
    GKRAddress.BaseLayerWitness 88, GKRAddress.BaseLayerWitness 89, GKRAddress.BaseLayerWitness 90,
    GKRAddress.BaseLayerWitness 91, GKRAddress.BaseLayerWitness 92, GKRAddress.BaseLayerWitness 93,
    GKRAddress.BaseLayerWitness 94, GKRAddress.BaseLayerWitness 95, GKRAddress.BaseLayerWitness 96,
    GKRAddress.BaseLayerWitness 97, GKRAddress.BaseLayerWitness 98, GKRAddress.BaseLayerWitness 99,
    GKRAddress.BaseLayerWitness 100, GKRAddress.BaseLayerWitness 101, GKRAddress.BaseLayerWitness 102,
    GKRAddress.BaseLayerWitness 103, GKRAddress.BaseLayerWitness 104, GKRAddress.BaseLayerWitness 105,
    GKRAddress.BaseLayerWitness 106, GKRAddress.BaseLayerWitness 107, GKRAddress.BaseLayerWitness 108,
    GKRAddress.BaseLayerWitness 109, GKRAddress.BaseLayerWitness 110, GKRAddress.BaseLayerWitness 111,
    GKRAddress.BaseLayerWitness 112, GKRAddress.BaseLayerWitness 113, GKRAddress.BaseLayerWitness 114,
    GKRAddress.BaseLayerWitness 115, GKRAddress.BaseLayerWitness 116, GKRAddress.BaseLayerWitness 117,
    GKRAddress.BaseLayerWitness 118, GKRAddress.BaseLayerWitness 119, GKRAddress.BaseLayerWitness 120,
    GKRAddress.BaseLayerWitness 121, GKRAddress.BaseLayerWitness 122, GKRAddress.BaseLayerWitness 123,
    GKRAddress.BaseLayerWitness 124, GKRAddress.BaseLayerWitness 125, GKRAddress.BaseLayerWitness 126,
    GKRAddress.BaseLayerWitness 127, GKRAddress.BaseLayerWitness 128, GKRAddress.BaseLayerWitness 129,
    GKRAddress.BaseLayerWitness 130, GKRAddress.BaseLayerWitness 131, GKRAddress.BaseLayerWitness 132,
    GKRAddress.BaseLayerWitness 133, GKRAddress.BaseLayerWitness 134, GKRAddress.InnerLayer 1 21,
    GKRAddress.InnerLayer 1 22, GKRAddress.InnerLayer 1 23, GKRAddress.InnerLayer 1 24, GKRAddress.InnerLayer 1 25,
    GKRAddress.InnerLayer 1 26, GKRAddress.InnerLayer 1 27, GKRAddress.InnerLayer 1 28, GKRAddress.InnerLayer 1 29,
    GKRAddress.InnerLayer 1 30, GKRAddress.InnerLayer 1 31, GKRAddress.InnerLayer 1 32, GKRAddress.InnerLayer 1 33,
    GKRAddress.InnerLayer 1 34, GKRAddress.InnerLayer 1 35, GKRAddress.InnerLayer 1 36, GKRAddress.InnerLayer 1 37,
    GKRAddress.BaseLayerWitness 135, GKRAddress.BaseLayerWitness 136, GKRAddress.InnerLayer 1 38,
    GKRAddress.InnerLayer 1 39, GKRAddress.BaseLayerWitness 137, GKRAddress.BaseLayerMemory 0,
    GKRAddress.BaseLayerMemory 1, GKRAddress.BaseLayerWitness 138, GKRAddress.BaseLayerMemory 4,
    GKRAddress.BaseLayerMemory 5, GKRAddress.BaseLayerWitness 139, GKRAddress.BaseLayerMemory 10,
    GKRAddress.BaseLayerMemory 11, GKRAddress.BaseLayerWitness 140, GKRAddress.BaseLayerMemory 16,
    GKRAddress.BaseLayerMemory 17, GKRAddress.BaseLayerWitness 141, GKRAddress.BaseLayerMemory 22,
    GKRAddress.BaseLayerMemory 23, GKRAddress.BaseLayerWitness 142, GKRAddress.BaseLayerMemory 28,
    GKRAddress.BaseLayerMemory 29, GKRAddress.BaseLayerWitness 143, GKRAddress.BaseLayerMemory 34,
    GKRAddress.BaseLayerMemory 35, GKRAddress.BaseLayerWitness 144, GKRAddress.BaseLayerMemory 40,
    GKRAddress.BaseLayerMemory 41, GKRAddress.BaseLayerWitness 145, GKRAddress.BaseLayerMemory 46,
    GKRAddress.BaseLayerMemory 47, GKRAddress.BaseLayerWitness 146, GKRAddress.BaseLayerMemory 52,
    GKRAddress.BaseLayerMemory 53, GKRAddress.BaseLayerWitness 147, GKRAddress.BaseLayerMemory 56,
    GKRAddress.BaseLayerMemory 57, GKRAddress.BaseLayerWitness 148, GKRAddress.BaseLayerMemory 60,
    GKRAddress.BaseLayerMemory 61, GKRAddress.BaseLayerWitness 149, GKRAddress.BaseLayerMemory 64,
    GKRAddress.BaseLayerMemory 65, GKRAddress.BaseLayerWitness 150, GKRAddress.BaseLayerMemory 68,
    GKRAddress.BaseLayerMemory 69, GKRAddress.BaseLayerWitness 151, GKRAddress.BaseLayerMemory 72,
    GKRAddress.BaseLayerMemory 73, GKRAddress.BaseLayerWitness 152, GKRAddress.BaseLayerMemory 76,
    GKRAddress.BaseLayerMemory 77, GKRAddress.BaseLayerWitness 153, GKRAddress.BaseLayerMemory 80,
    GKRAddress.BaseLayerMemory 81, GKRAddress.BaseLayerWitness 154, GKRAddress.BaseLayerMemory 84,
    GKRAddress.BaseLayerMemory 85, GKRAddress.BaseLayerWitness 155, GKRAddress.BaseLayerMemory 88,
    GKRAddress.BaseLayerMemory 89, GKRAddress.BaseLayerWitness 156, GKRAddress.BaseLayerWitness 157,
    GKRAddress.BaseLayerWitness 158, GKRAddress.BaseLayerWitness 159]

theorem native.placementsRange : native.placementKeys = List.range 276 := by kernel_rfl

theorem native.placementsUnique : (native.placementKeys).Nodup :=
  by
  rw [native.placementsRange]
  exact List.nodup_range

theorem native.placementsSourceBinding :
    native.placementAddresses = Airbender.Compiler.CleanPlacementNative.BigintCached.placements := by kernel_rfl

theorem native.placementsInBank :
    ((native.placementAddresses).all fun address : GKRAddress =>
        decide
          ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
              ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
            address)) =
      true :=
  (congrArg
        (fun items : List GKRAddress =>
          items.all fun address : GKRAddress =>
            decide
              ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
                  ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
                address))
        native.placementsSourceBinding).trans
    Airbender.Compiler.CleanPlacementNative.BigintCached.placementsInBank

theorem native.placementInBank0 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 94) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 0 (GKRAddress.BaseLayerMemory 94) (by rfl)

theorem native.placementInBank1 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 95) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 1 (GKRAddress.BaseLayerMemory 95) (by rfl)

theorem native.placementInBank2 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 96) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 2 (GKRAddress.BaseLayerMemory 96) (by rfl)

theorem native.placementInBank3 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 2) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 3 (GKRAddress.BaseLayerMemory 2) (by rfl)

theorem native.placementInBank4 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 3) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 4 (GKRAddress.BaseLayerMemory 3) (by rfl)

theorem native.placementInBank5 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 6) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 5 (GKRAddress.BaseLayerMemory 6) (by rfl)

theorem native.placementInBank6 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 7) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 6 (GKRAddress.BaseLayerMemory 7) (by rfl)

theorem native.placementInBank7 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 8) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 7 (GKRAddress.BaseLayerMemory 8) (by rfl)

theorem native.placementInBank8 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 9) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 8 (GKRAddress.BaseLayerMemory 9) (by rfl)

theorem native.placementInBank9 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 12) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 9 (GKRAddress.BaseLayerMemory 12) (by rfl)

theorem native.placementInBank10 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 13) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 10 (GKRAddress.BaseLayerMemory 13) (by rfl)

theorem native.placementInBank11 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 14) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 11 (GKRAddress.BaseLayerMemory 14) (by rfl)

theorem native.placementInBank12 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 15) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 12 (GKRAddress.BaseLayerMemory 15) (by rfl)

theorem native.placementInBank13 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 18) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 13 (GKRAddress.BaseLayerMemory 18) (by rfl)

theorem native.placementInBank14 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 19) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 14 (GKRAddress.BaseLayerMemory 19) (by rfl)

theorem native.placementInBank15 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 20) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 15 (GKRAddress.BaseLayerMemory 20) (by rfl)

theorem native.placementInBank16 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 21) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 16 (GKRAddress.BaseLayerMemory 21) (by rfl)
end Airbender.Compiler.CleanArithmeticNative.BigintCached
