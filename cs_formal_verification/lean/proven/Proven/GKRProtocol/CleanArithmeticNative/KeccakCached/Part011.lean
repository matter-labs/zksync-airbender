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

local instance generatedBatch11Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch11Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

theorem native.placementInBank257 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerWitness 170) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 257 (GKRAddress.BaseLayerWitness 170) (by rfl)

theorem native.placementInBank258 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 75) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 258 (GKRAddress.BaseLayerMemory 75) (by rfl)

theorem native.placementInBank259 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 76) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 259 (GKRAddress.BaseLayerMemory 76) (by rfl)

theorem native.placementInBank260 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerWitness 171) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 260 (GKRAddress.BaseLayerWitness 171) (by rfl)

theorem native.placementInBank261 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 82) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 261 (GKRAddress.BaseLayerMemory 82) (by rfl)

theorem native.placementInBank262 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 83) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 262 (GKRAddress.BaseLayerMemory 83) (by rfl)

theorem native.placementInBank263 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerWitness 172) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 263 (GKRAddress.BaseLayerWitness 172) (by rfl)

theorem native.placementInBank264 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerWitness 173) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 264 (GKRAddress.BaseLayerWitness 173) (by rfl)

theorem native.placementInBank265 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerWitness 174) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 265 (GKRAddress.BaseLayerWitness 174) (by rfl)
end Airbender.Compiler.CleanArithmeticNative.KeccakCached
