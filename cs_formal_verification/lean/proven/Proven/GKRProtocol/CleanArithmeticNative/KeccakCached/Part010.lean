module
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part000
public import Proven.KernelRfl
import all Mathlib.Data.List.Sort
public import Proven.Import.GKRProtocol.CleanArithmeticImport
public import Proven.GKRProtocol.CleanIdealNative.KeccakCached
public import Proven.GKRProtocol.FullArithmeticNative.KeccakCached
public import Proven.GKRProtocol.CleanPlacementNative.KeccakCached

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.CleanArithmeticNative.KeccakCached
open Airbender Airbender.Compiler
set_option maxRecDepth 32768

local instance generatedBatch10Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch10Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

theorem native.placementInBank233 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerWitness 162) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 233 (GKRAddress.BaseLayerWitness 162) (by rfl)

theorem native.placementInBank234 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 23) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 234 (GKRAddress.BaseLayerMemory 23) (by rfl)

theorem native.placementInBank235 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 24) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 235 (GKRAddress.BaseLayerMemory 24) (by rfl)

theorem native.placementInBank236 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerWitness 163) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 236 (GKRAddress.BaseLayerWitness 163) (by rfl)

theorem native.placementInBank237 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 30) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 237 (GKRAddress.BaseLayerMemory 30) (by rfl)

theorem native.placementInBank238 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 31) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 238 (GKRAddress.BaseLayerMemory 31) (by rfl)

theorem native.placementInBank239 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerWitness 164) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 239 (GKRAddress.BaseLayerWitness 164) (by rfl)

theorem native.placementInBank240 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 36) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 240 (GKRAddress.BaseLayerMemory 36) (by rfl)

theorem native.placementInBank241 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 37) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 241 (GKRAddress.BaseLayerMemory 37) (by rfl)

theorem native.placementInBank242 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerWitness 165) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 242 (GKRAddress.BaseLayerWitness 165) (by rfl)

theorem native.placementInBank243 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 43) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 243 (GKRAddress.BaseLayerMemory 43) (by rfl)

theorem native.placementInBank244 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 44) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 244 (GKRAddress.BaseLayerMemory 44) (by rfl)

theorem native.placementInBank245 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerWitness 166) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 245 (GKRAddress.BaseLayerWitness 166) (by rfl)

theorem native.placementInBank246 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 49) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 246 (GKRAddress.BaseLayerMemory 49) (by rfl)

theorem native.placementInBank247 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 50) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 247 (GKRAddress.BaseLayerMemory 50) (by rfl)

theorem native.placementInBank248 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerWitness 167) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 248 (GKRAddress.BaseLayerWitness 167) (by rfl)

theorem native.placementInBank249 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 56) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 249 (GKRAddress.BaseLayerMemory 56) (by rfl)

theorem native.placementInBank250 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 57) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 250 (GKRAddress.BaseLayerMemory 57) (by rfl)

theorem native.placementInBank251 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerWitness 168) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 251 (GKRAddress.BaseLayerWitness 168) (by rfl)

theorem native.placementInBank252 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 62) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 252 (GKRAddress.BaseLayerMemory 62) (by rfl)

theorem native.placementInBank253 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 63) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 253 (GKRAddress.BaseLayerMemory 63) (by rfl)

theorem native.placementInBank254 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerWitness 169) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 254 (GKRAddress.BaseLayerWitness 169) (by rfl)

theorem native.placementInBank255 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 69) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 255 (GKRAddress.BaseLayerMemory 69) (by rfl)

theorem native.placementInBank256 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 70) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 256 (GKRAddress.BaseLayerMemory 70) (by rfl)
end Airbender.Compiler.CleanArithmeticNative.KeccakCached
