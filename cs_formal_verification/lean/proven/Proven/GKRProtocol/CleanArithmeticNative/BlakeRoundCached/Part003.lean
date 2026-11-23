module
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part000
import all Mathlib.Data.List.Sort
public import Proven.Import.GKRProtocol.CleanArithmeticImport
public import Proven.GKRProtocol.CleanIdealNative.BlakeRoundCached
public import Proven.GKRProtocol.FullArithmeticNative.BlakeRoundCached
public import Proven.GKRProtocol.CleanPlacementNative.BlakeRoundCached

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached
open Airbender Airbender.Compiler
set_option maxRecDepth 32768

local instance generatedBatch3Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch3Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

theorem native.placementInBank58 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 85) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 58 (GKRAddress.BaseLayerMemory 85) (by cbv)

theorem native.placementInBank59 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 86) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 59 (GKRAddress.BaseLayerMemory 86) (by cbv)

theorem native.placementInBank60 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 87) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 60 (GKRAddress.BaseLayerMemory 87) (by cbv)

theorem native.placementInBank61 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 90) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 61 (GKRAddress.BaseLayerMemory 90) (by cbv)

theorem native.placementInBank62 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 91) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 62 (GKRAddress.BaseLayerMemory 91) (by cbv)

theorem native.placementInBank63 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 92) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 63 (GKRAddress.BaseLayerMemory 92) (by cbv)

theorem native.placementInBank64 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 93) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 64 (GKRAddress.BaseLayerMemory 93) (by cbv)

theorem native.placementInBank65 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 96) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 65 (GKRAddress.BaseLayerMemory 96) (by cbv)

theorem native.placementInBank66 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 97) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 66 (GKRAddress.BaseLayerMemory 97) (by cbv)

theorem native.placementInBank67 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 98) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 67 (GKRAddress.BaseLayerMemory 98) (by cbv)

theorem native.placementInBank68 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 99) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 68 (GKRAddress.BaseLayerMemory 99) (by cbv)

theorem native.placementInBank69 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 102) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 69 (GKRAddress.BaseLayerMemory 102) (by cbv)

theorem native.placementInBank70 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 103) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 70 (GKRAddress.BaseLayerMemory 103) (by cbv)

theorem native.placementInBank71 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 104) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 71 (GKRAddress.BaseLayerMemory 104) (by cbv)

theorem native.placementInBank72 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 105) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 72 (GKRAddress.BaseLayerMemory 105) (by cbv)

theorem native.placementInBank73 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 108) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 73 (GKRAddress.BaseLayerMemory 108) (by cbv)

theorem native.placementInBank74 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 109) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 74 (GKRAddress.BaseLayerMemory 109) (by cbv)

theorem native.placementInBank75 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 110) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 75 (GKRAddress.BaseLayerMemory 110) (by cbv)

theorem native.placementInBank76 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 111) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 76 (GKRAddress.BaseLayerMemory 111) (by cbv)

theorem native.placementInBank77 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 114) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 77 (GKRAddress.BaseLayerMemory 114) (by cbv)

theorem native.placementInBank78 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 115) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 78 (GKRAddress.BaseLayerMemory 115) (by cbv)

theorem native.placementInBank79 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 116) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 79 (GKRAddress.BaseLayerMemory 116) (by cbv)

theorem native.placementInBank80 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 117) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 80 (GKRAddress.BaseLayerMemory 117) (by cbv)

theorem native.placementInBank81 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 120) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 81 (GKRAddress.BaseLayerMemory 120) (by cbv)
end Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached
