module
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part000
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

local instance generatedBatch11Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch11Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

theorem native.placementInBank257 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerWitness 151) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 257 (GKRAddress.BaseLayerWitness 151) (by rfl)

theorem native.placementInBank258 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 72) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 258 (GKRAddress.BaseLayerMemory 72) (by rfl)

theorem native.placementInBank259 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 73) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 259 (GKRAddress.BaseLayerMemory 73) (by rfl)

theorem native.placementInBank260 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerWitness 152) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 260 (GKRAddress.BaseLayerWitness 152) (by rfl)

theorem native.placementInBank261 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 76) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 261 (GKRAddress.BaseLayerMemory 76) (by rfl)

theorem native.placementInBank262 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 77) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 262 (GKRAddress.BaseLayerMemory 77) (by rfl)

theorem native.placementInBank263 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerWitness 153) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 263 (GKRAddress.BaseLayerWitness 153) (by rfl)

theorem native.placementInBank264 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 80) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 264 (GKRAddress.BaseLayerMemory 80) (by rfl)

theorem native.placementInBank265 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 81) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 265 (GKRAddress.BaseLayerMemory 81) (by rfl)

theorem native.placementInBank266 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerWitness 154) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 266 (GKRAddress.BaseLayerWitness 154) (by rfl)

theorem native.placementInBank267 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 84) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 267 (GKRAddress.BaseLayerMemory 84) (by rfl)

theorem native.placementInBank268 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 85) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 268 (GKRAddress.BaseLayerMemory 85) (by rfl)

theorem native.placementInBank269 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerWitness 155) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 269 (GKRAddress.BaseLayerWitness 155) (by rfl)

theorem native.placementInBank270 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 88) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 270 (GKRAddress.BaseLayerMemory 88) (by rfl)

theorem native.placementInBank271 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 89) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 271 (GKRAddress.BaseLayerMemory 89) (by rfl)

theorem native.placementInBank272 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerWitness 156) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 272 (GKRAddress.BaseLayerWitness 156) (by rfl)

theorem native.placementInBank273 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerWitness 157) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 273 (GKRAddress.BaseLayerWitness 157) (by rfl)

theorem native.placementInBank274 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerWitness 158) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 274 (GKRAddress.BaseLayerWitness 158) (by rfl)

theorem native.placementInBank275 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerWitness 159) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 275 (GKRAddress.BaseLayerWitness 159) (by rfl)
end Airbender.Compiler.CleanArithmeticNative.BigintCached
