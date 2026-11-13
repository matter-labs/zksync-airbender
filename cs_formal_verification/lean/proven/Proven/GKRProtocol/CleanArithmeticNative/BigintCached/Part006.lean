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

local instance generatedBatch6Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch6Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

theorem native.placementInBank137 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerWitness 78) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 137 (GKRAddress.BaseLayerWitness 78) (by rfl)

theorem native.placementInBank138 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerWitness 79) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 138 (GKRAddress.BaseLayerWitness 79) (by rfl)

theorem native.placementInBank139 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerWitness 80) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 139 (GKRAddress.BaseLayerWitness 80) (by rfl)

theorem native.placementInBank140 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerWitness 81) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 140 (GKRAddress.BaseLayerWitness 81) (by rfl)

theorem native.placementInBank141 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerWitness 82) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 141 (GKRAddress.BaseLayerWitness 82) (by rfl)

theorem native.placementInBank142 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerWitness 83) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 142 (GKRAddress.BaseLayerWitness 83) (by rfl)

theorem native.placementInBank143 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerWitness 84) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 143 (GKRAddress.BaseLayerWitness 84) (by rfl)

theorem native.placementInBank144 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerWitness 85) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 144 (GKRAddress.BaseLayerWitness 85) (by rfl)

theorem native.placementInBank145 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerWitness 86) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 145 (GKRAddress.BaseLayerWitness 86) (by rfl)

theorem native.placementInBank146 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerWitness 87) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 146 (GKRAddress.BaseLayerWitness 87) (by rfl)

theorem native.placementInBank147 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerWitness 88) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 147 (GKRAddress.BaseLayerWitness 88) (by rfl)

theorem native.placementInBank148 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerWitness 89) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 148 (GKRAddress.BaseLayerWitness 89) (by rfl)

theorem native.placementInBank149 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerWitness 90) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 149 (GKRAddress.BaseLayerWitness 90) (by rfl)

theorem native.placementInBank150 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerWitness 91) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 150 (GKRAddress.BaseLayerWitness 91) (by rfl)

theorem native.placementInBank151 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerWitness 92) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 151 (GKRAddress.BaseLayerWitness 92) (by rfl)

theorem native.placementInBank152 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerWitness 93) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 152 (GKRAddress.BaseLayerWitness 93) (by rfl)

theorem native.placementInBank153 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerWitness 94) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 153 (GKRAddress.BaseLayerWitness 94) (by rfl)

theorem native.placementInBank154 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerWitness 95) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 154 (GKRAddress.BaseLayerWitness 95) (by rfl)

theorem native.placementInBank155 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerWitness 96) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 155 (GKRAddress.BaseLayerWitness 96) (by rfl)

theorem native.placementInBank156 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerWitness 97) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 156 (GKRAddress.BaseLayerWitness 97) (by rfl)

theorem native.placementInBank157 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerWitness 98) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 157 (GKRAddress.BaseLayerWitness 98) (by rfl)

theorem native.placementInBank158 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerWitness 99) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 158 (GKRAddress.BaseLayerWitness 99) (by rfl)

theorem native.placementInBank159 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerWitness 100) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 159 (GKRAddress.BaseLayerWitness 100) (by rfl)

theorem native.placementInBank160 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerWitness 101) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 160 (GKRAddress.BaseLayerWitness 101) (by rfl)
end Airbender.Compiler.CleanArithmeticNative.BigintCached
