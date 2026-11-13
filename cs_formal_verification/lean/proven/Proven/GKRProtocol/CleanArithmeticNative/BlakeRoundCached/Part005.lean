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

local instance generatedBatch5Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch5Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

theorem native.placementInBank106 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 159) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 106 (GKRAddress.BaseLayerMemory 159) (by rfl)

theorem native.placementInBank107 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 162) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 107 (GKRAddress.BaseLayerMemory 162) (by rfl)

theorem native.placementInBank108 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 163) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 108 (GKRAddress.BaseLayerMemory 163) (by rfl)

theorem native.placementInBank109 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 166) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 109 (GKRAddress.BaseLayerMemory 166) (by rfl)

theorem native.placementInBank110 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 167) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 110 (GKRAddress.BaseLayerMemory 167) (by rfl)

theorem native.placementInBank111 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 170) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 111 (GKRAddress.BaseLayerMemory 170) (by rfl)

theorem native.placementInBank112 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 171) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 112 (GKRAddress.BaseLayerMemory 171) (by rfl)

theorem native.placementInBank113 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 174) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 113 (GKRAddress.BaseLayerMemory 174) (by rfl)

theorem native.placementInBank114 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 175) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 114 (GKRAddress.BaseLayerMemory 175) (by rfl)

theorem native.placementInBank115 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 178) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 115 (GKRAddress.BaseLayerMemory 178) (by rfl)

theorem native.placementInBank116 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 179) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 116 (GKRAddress.BaseLayerMemory 179) (by rfl)

theorem native.placementInBank117 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 182) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 117 (GKRAddress.BaseLayerMemory 182) (by rfl)

theorem native.placementInBank118 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 183) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 118 (GKRAddress.BaseLayerMemory 183) (by rfl)

theorem native.placementInBank119 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 186) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 119 (GKRAddress.BaseLayerMemory 186) (by rfl)

theorem native.placementInBank120 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 187) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 120 (GKRAddress.BaseLayerMemory 187) (by rfl)

theorem native.placementInBank121 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 190) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 121 (GKRAddress.BaseLayerMemory 190) (by rfl)

theorem native.placementInBank122 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 191) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 122 (GKRAddress.BaseLayerMemory 191) (by rfl)

theorem native.placementInBank123 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 194) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 123 (GKRAddress.BaseLayerMemory 194) (by rfl)

theorem native.placementInBank124 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 195) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 124 (GKRAddress.BaseLayerMemory 195) (by rfl)

theorem native.placementInBank125 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 198) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 125 (GKRAddress.BaseLayerMemory 198) (by rfl)

theorem native.placementInBank126 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 199) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 126 (GKRAddress.BaseLayerMemory 199) (by rfl)

theorem native.placementInBank127 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 202) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 127 (GKRAddress.BaseLayerMemory 202) (by rfl)

theorem native.placementInBank128 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 203) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 128 (GKRAddress.BaseLayerMemory 203) (by rfl)

theorem native.placementInBank129 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 206) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 129 (GKRAddress.BaseLayerMemory 206) (by rfl)
end Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached
