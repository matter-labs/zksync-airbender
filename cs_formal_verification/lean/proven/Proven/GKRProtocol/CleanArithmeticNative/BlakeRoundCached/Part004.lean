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

local instance generatedBatch4Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch4Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

theorem native.placementInBank82 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 121) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 82 (GKRAddress.BaseLayerMemory 121) (by rfl)

theorem native.placementInBank83 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 122) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 83 (GKRAddress.BaseLayerMemory 122) (by rfl)

theorem native.placementInBank84 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 123) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 84 (GKRAddress.BaseLayerMemory 123) (by rfl)

theorem native.placementInBank85 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 126) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 85 (GKRAddress.BaseLayerMemory 126) (by rfl)

theorem native.placementInBank86 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 127) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 86 (GKRAddress.BaseLayerMemory 127) (by rfl)

theorem native.placementInBank87 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 128) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 87 (GKRAddress.BaseLayerMemory 128) (by rfl)

theorem native.placementInBank88 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 129) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 88 (GKRAddress.BaseLayerMemory 129) (by rfl)

theorem native.placementInBank89 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 132) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 89 (GKRAddress.BaseLayerMemory 132) (by rfl)

theorem native.placementInBank90 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 133) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 90 (GKRAddress.BaseLayerMemory 133) (by rfl)

theorem native.placementInBank91 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 134) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 91 (GKRAddress.BaseLayerMemory 134) (by rfl)

theorem native.placementInBank92 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 135) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 92 (GKRAddress.BaseLayerMemory 135) (by rfl)

theorem native.placementInBank93 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 138) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 93 (GKRAddress.BaseLayerMemory 138) (by rfl)

theorem native.placementInBank94 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 139) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 94 (GKRAddress.BaseLayerMemory 139) (by rfl)

theorem native.placementInBank95 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 140) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 95 (GKRAddress.BaseLayerMemory 140) (by rfl)

theorem native.placementInBank96 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 141) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 96 (GKRAddress.BaseLayerMemory 141) (by rfl)

theorem native.placementInBank97 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 144) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 97 (GKRAddress.BaseLayerMemory 144) (by rfl)

theorem native.placementInBank98 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 145) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 98 (GKRAddress.BaseLayerMemory 145) (by rfl)

theorem native.placementInBank99 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 146) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 99 (GKRAddress.BaseLayerMemory 146) (by rfl)

theorem native.placementInBank100 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 147) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 100 (GKRAddress.BaseLayerMemory 147) (by rfl)

theorem native.placementInBank101 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 150) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 101 (GKRAddress.BaseLayerMemory 150) (by rfl)

theorem native.placementInBank102 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 151) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 102 (GKRAddress.BaseLayerMemory 151) (by rfl)

theorem native.placementInBank103 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 154) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 103 (GKRAddress.BaseLayerMemory 154) (by rfl)

theorem native.placementInBank104 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 155) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 104 (GKRAddress.BaseLayerMemory 155) (by rfl)

theorem native.placementInBank105 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 158) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 105 (GKRAddress.BaseLayerMemory 158) (by rfl)
end Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached
