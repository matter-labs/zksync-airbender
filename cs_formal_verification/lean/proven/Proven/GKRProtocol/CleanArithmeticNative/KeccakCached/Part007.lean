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

local instance generatedBatch7Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch7Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

theorem native.placementInBank161 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerWitness 98) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 161 (GKRAddress.BaseLayerWitness 98) (by rfl)

theorem native.placementInBank162 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerWitness 99) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 162 (GKRAddress.BaseLayerWitness 99) (by rfl)

theorem native.placementInBank163 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerWitness 100) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 163 (GKRAddress.BaseLayerWitness 100) (by rfl)

theorem native.placementInBank164 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerWitness 101) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 164 (GKRAddress.BaseLayerWitness 101) (by rfl)

theorem native.placementInBank165 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerWitness 102) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 165 (GKRAddress.BaseLayerWitness 102) (by rfl)

theorem native.placementInBank166 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerWitness 103) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 166 (GKRAddress.BaseLayerWitness 103) (by rfl)

theorem native.placementInBank167 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerWitness 104) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 167 (GKRAddress.BaseLayerWitness 104) (by rfl)

theorem native.placementInBank168 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerWitness 105) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 168 (GKRAddress.BaseLayerWitness 105) (by rfl)

theorem native.placementInBank169 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerWitness 106) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 169 (GKRAddress.BaseLayerWitness 106) (by rfl)

theorem native.placementInBank170 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerWitness 107) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 170 (GKRAddress.BaseLayerWitness 107) (by rfl)

theorem native.placementInBank171 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerWitness 108) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 171 (GKRAddress.BaseLayerWitness 108) (by rfl)

theorem native.placementInBank172 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerWitness 109) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 172 (GKRAddress.BaseLayerWitness 109) (by rfl)

theorem native.placementInBank173 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerWitness 110) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 173 (GKRAddress.BaseLayerWitness 110) (by rfl)

theorem native.placementInBank174 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerWitness 111) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 174 (GKRAddress.BaseLayerWitness 111) (by rfl)

theorem native.placementInBank175 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerWitness 112) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 175 (GKRAddress.BaseLayerWitness 112) (by rfl)

theorem native.placementInBank176 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerWitness 113) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 176 (GKRAddress.BaseLayerWitness 113) (by rfl)

theorem native.placementInBank177 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerWitness 114) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 177 (GKRAddress.BaseLayerWitness 114) (by rfl)

theorem native.placementInBank178 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerWitness 115) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 178 (GKRAddress.BaseLayerWitness 115) (by rfl)

theorem native.placementInBank179 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerWitness 116) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 179 (GKRAddress.BaseLayerWitness 116) (by rfl)

theorem native.placementInBank180 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerWitness 117) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 180 (GKRAddress.BaseLayerWitness 117) (by rfl)

theorem native.placementInBank181 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerWitness 118) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 181 (GKRAddress.BaseLayerWitness 118) (by rfl)

theorem native.placementInBank182 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerWitness 119) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 182 (GKRAddress.BaseLayerWitness 119) (by rfl)

theorem native.placementInBank183 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerWitness 120) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 183 (GKRAddress.BaseLayerWitness 120) (by rfl)

theorem native.placementInBank184 :
    (fun address : GKRAddress =>
          decide
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
                ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
              address))
        (GKRAddress.BaseLayerWitness 121) =
      true :=
  CleanPlacementChecks.all_lookup
    (fun address : GKRAddress =>
      decide
        ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address
            ((Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement address) =
          address))
    native.placementAddresses native.placementsInBank 184 (GKRAddress.BaseLayerWitness 121) (by rfl)
end Airbender.Compiler.CleanArithmeticNative.KeccakCached
