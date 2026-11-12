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

local instance generatedBatch1Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch1Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

theorem native.placementInBank17 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 24) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 17 (GKRAddress.BaseLayerMemory 24) (by rfl)

theorem native.placementInBank18 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 25) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 18 (GKRAddress.BaseLayerMemory 25) (by rfl)

theorem native.placementInBank19 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 26) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 19 (GKRAddress.BaseLayerMemory 26) (by rfl)

theorem native.placementInBank20 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 27) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 20 (GKRAddress.BaseLayerMemory 27) (by rfl)

theorem native.placementInBank21 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 30) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 21 (GKRAddress.BaseLayerMemory 30) (by rfl)

theorem native.placementInBank22 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 31) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 22 (GKRAddress.BaseLayerMemory 31) (by rfl)

theorem native.placementInBank23 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 32) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 23 (GKRAddress.BaseLayerMemory 32) (by rfl)

theorem native.placementInBank24 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 33) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 24 (GKRAddress.BaseLayerMemory 33) (by rfl)

theorem native.placementInBank25 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 36) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 25 (GKRAddress.BaseLayerMemory 36) (by rfl)

theorem native.placementInBank26 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 37) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 26 (GKRAddress.BaseLayerMemory 37) (by rfl)

theorem native.placementInBank27 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 38) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 27 (GKRAddress.BaseLayerMemory 38) (by rfl)

theorem native.placementInBank28 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 39) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 28 (GKRAddress.BaseLayerMemory 39) (by rfl)

theorem native.placementInBank29 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 42) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 29 (GKRAddress.BaseLayerMemory 42) (by rfl)

theorem native.placementInBank30 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 43) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 30 (GKRAddress.BaseLayerMemory 43) (by rfl)

theorem native.placementInBank31 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 44) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 31 (GKRAddress.BaseLayerMemory 44) (by rfl)

theorem native.placementInBank32 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 45) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 32 (GKRAddress.BaseLayerMemory 45) (by rfl)

theorem native.placementInBank33 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 48) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 33 (GKRAddress.BaseLayerMemory 48) (by rfl)

theorem native.placementInBank34 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 49) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 34 (GKRAddress.BaseLayerMemory 49) (by rfl)

theorem native.placementInBank35 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 50) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 35 (GKRAddress.BaseLayerMemory 50) (by rfl)

theorem native.placementInBank36 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 51) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 36 (GKRAddress.BaseLayerMemory 51) (by rfl)

theorem native.placementInBank37 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 54) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 37 (GKRAddress.BaseLayerMemory 54) (by rfl)

theorem native.placementInBank38 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 55) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 38 (GKRAddress.BaseLayerMemory 55) (by rfl)

theorem native.placementInBank39 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 58) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 39 (GKRAddress.BaseLayerMemory 58) (by rfl)

theorem native.placementInBank40 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerMemory 59) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 40 (GKRAddress.BaseLayerMemory 59) (by rfl)
end Airbender.Compiler.CleanArithmeticNative.BigintCached
