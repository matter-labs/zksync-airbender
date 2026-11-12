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

local instance generatedBatch3Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch3Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

theorem native.placementInBank65 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerWitness 2) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 65 (GKRAddress.BaseLayerWitness 2) (by rfl)

theorem native.placementInBank66 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerWitness 3) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 66 (GKRAddress.BaseLayerWitness 3) (by rfl)

theorem native.placementInBank67 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerWitness 4) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 67 (GKRAddress.BaseLayerWitness 4) (by rfl)

theorem native.placementInBank68 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerWitness 5) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 68 (GKRAddress.BaseLayerWitness 5) (by rfl)

theorem native.placementInBank69 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerWitness 6) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 69 (GKRAddress.BaseLayerWitness 6) (by rfl)

theorem native.placementInBank70 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerWitness 7) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 70 (GKRAddress.BaseLayerWitness 7) (by rfl)

theorem native.placementInBank71 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerWitness 8) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 71 (GKRAddress.BaseLayerWitness 8) (by rfl)

theorem native.placementInBank72 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerWitness 9) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 72 (GKRAddress.BaseLayerWitness 9) (by rfl)

theorem native.placementInBank73 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerWitness 10) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 73 (GKRAddress.BaseLayerWitness 10) (by rfl)

theorem native.placementInBank74 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerWitness 11) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 74 (GKRAddress.BaseLayerWitness 11) (by rfl)

theorem native.placementInBank75 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerWitness 12) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 75 (GKRAddress.BaseLayerWitness 12) (by rfl)

theorem native.placementInBank76 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerWitness 13) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 76 (GKRAddress.BaseLayerWitness 13) (by rfl)

theorem native.placementInBank77 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerWitness 14) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 77 (GKRAddress.BaseLayerWitness 14) (by rfl)

theorem native.placementInBank78 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerWitness 15) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 78 (GKRAddress.BaseLayerWitness 15) (by rfl)

theorem native.placementInBank79 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerWitness 16) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 79 (GKRAddress.BaseLayerWitness 16) (by rfl)

theorem native.placementInBank80 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerWitness 17) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 80 (GKRAddress.BaseLayerWitness 17) (by rfl)

theorem native.placementInBank81 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerWitness 18) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 81 (GKRAddress.BaseLayerWitness 18) (by rfl)

theorem native.placementInBank82 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerWitness 19) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 82 (GKRAddress.BaseLayerWitness 19) (by rfl)

theorem native.placementInBank83 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerWitness 20) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 83 (GKRAddress.BaseLayerWitness 20) (by rfl)

theorem native.placementInBank84 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerWitness 21) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 84 (GKRAddress.BaseLayerWitness 21) (by rfl)

theorem native.placementInBank85 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerWitness 22) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 85 (GKRAddress.BaseLayerWitness 22) (by rfl)

theorem native.placementInBank86 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerWitness 23) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 86 (GKRAddress.BaseLayerWitness 23) (by rfl)

theorem native.placementInBank87 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerWitness 24) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 87 (GKRAddress.BaseLayerWitness 24) (by rfl)

theorem native.placementInBank88 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerWitness 25) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 88 (GKRAddress.BaseLayerWitness 25) (by rfl)
end Airbender.Compiler.CleanArithmeticNative.KeccakCached
