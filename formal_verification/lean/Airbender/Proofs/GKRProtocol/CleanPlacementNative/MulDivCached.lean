import Airbender.Proofs.GKRProtocol.CleanPlacementChecks
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport
import Airbender.Proofs.GKRProtocol.FullArithmeticNative.MulDivCached

namespace Airbender.Compiler.CleanPlacementNative.MulDivCached
open Airbender Airbender.Compiler NumericPolynomialChecks
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

def bankCodes0 : List Nat := [325, 362, 401, 442, 290, 17, 82, 197, 0, 1, 4, 9, 16, 25, 485, 530]
def bankCodes1 : List Nat := [577, 626, 2, 3, 5, 10, 26, 37, 50, 65, 145, 170, 226, 257, 101, 122]
def bankCodes2 : List Nat := [36, 49, 64, 81, 100, 121, 144, 169, 196, 225, 256, 289, 678, 1371, 2502, 4227]
def bankCodes3 : List Nat := [6726, 10203, 14886, 21027, 28902, 38811, 51078, 66051, 84102, 105627, 131046, 160803, 195366, 235227, 280902, 332931]
def bankCodes4 : List Nat := [391878, 324, 361, 400, 441, 484, 529, 8, 1338651, 3422502, 28567, 38, 4102, 6567, 10006, 14647]
def bankCodes5 : List Nat := [20742]

def bank : LookupTable Nat := (LookupTable.branch 48 (LookupTable.branch 16 (LookupTable.leaf bankCodes0) (LookupTable.branch 16 (LookupTable.leaf bankCodes1) (LookupTable.leaf bankCodes2))) (LookupTable.branch 16 (LookupTable.leaf bankCodes3) (LookupTable.branch 16 (LookupTable.leaf bankCodes4) (LookupTable.leaf bankCodes5))))
def placements : List GKRAddress := [(.BaseLayerMemory 18), (.BaseLayerMemory 19), (.BaseLayerMemory 20), (.BaseLayerMemory 21), (.BaseLayerMemory 17), (.BaseLayerMemory 4), (.BaseLayerMemory 9), (.BaseLayerMemory 14), (.BaseLayerWitness 0), (.BaseLayerWitness 1), (.BaseLayerWitness 2), (.BaseLayerWitness 3), (.BaseLayerWitness 4), (.BaseLayerWitness 5), (.BaseLayerMemory 22), (.BaseLayerMemory 23), (.BaseLayerMemory 24), (.BaseLayerMemory 25), (.BaseLayerMemory 0), (.BaseLayerMemory 1), (.BaseLayerMemory 2), (.BaseLayerMemory 3), (.BaseLayerMemory 5), (.BaseLayerMemory 6), (.BaseLayerMemory 7), (.BaseLayerMemory 8), (.BaseLayerMemory 12), (.BaseLayerMemory 13), (.BaseLayerMemory 15), (.BaseLayerMemory 16), (.BaseLayerMemory 10), (.BaseLayerMemory 11), (.BaseLayerWitness 6), (.BaseLayerWitness 7), (.BaseLayerWitness 8), (.BaseLayerWitness 9), (.BaseLayerWitness 10), (.BaseLayerWitness 11), (.BaseLayerWitness 12), (.BaseLayerWitness 13), (.BaseLayerWitness 14), (.BaseLayerWitness 15), (.BaseLayerWitness 16), (.BaseLayerWitness 17), (.InnerLayer 1 5), (.InnerLayer 1 6), (.InnerLayer 1 7), (.InnerLayer 1 8), (.InnerLayer 1 9), (.InnerLayer 1 10), (.InnerLayer 1 11), (.InnerLayer 1 12), (.InnerLayer 1 13), (.InnerLayer 1 14), (.InnerLayer 1 15), (.InnerLayer 1 16), (.InnerLayer 1 17), (.InnerLayer 1 18), (.InnerLayer 1 19), (.InnerLayer 1 20), (.InnerLayer 1 21), (.InnerLayer 1 22), (.InnerLayer 1 23), (.InnerLayer 1 24), (.InnerLayer 1 25), (.BaseLayerWitness 18), (.BaseLayerWitness 19), (.BaseLayerWitness 20), (.BaseLayerWitness 21), (.BaseLayerWitness 22), (.BaseLayerWitness 23)]
def references : List (Nat × Nat) := [(325, 0), (362, 1), (401, 2), (442, 3), (290, 4), (17, 5), (82, 6), (197, 7), (0, 8), (1, 9), (4, 10), (9, 11), (16, 12), (25, 13), (485, 14), (530, 15), (577, 16), (626, 17), (2, 18), (3, 19), (5, 20), (10, 21), (26, 22), (37, 23), (50, 24), (65, 25), (145, 26), (170, 27), (226, 28), (257, 29), (101, 30), (122, 31), (36, 32), (49, 33), (64, 34), (81, 35), (100, 36), (121, 37), (144, 38), (169, 39), (196, 40), (225, 41), (256, 42), (289, 43), (678, 44), (1371, 45), (2502, 46), (4227, 47), (6726, 48), (10203, 49), (14886, 50), (21027, 51), (28902, 52), (38811, 53), (51078, 54), (66051, 55), (84102, 56), (105627, 57), (131046, 58), (160803, 59), (195366, 60), (235227, 61), (280902, 62), (332931, 63), (391878, 64), (324, 65), (361, 66), (400, 67), (441, 68), (484, 69), (529, 70)]
def capture : CleanPlacementChecks.Capture := ⟨bank, references⟩

numeric_data_binding bank_binding : bank.toList = Airbender.Compiler.FullArithmeticNative.MulDivCached.native.addresses.map AddressUniqueChecks.addressCode
numeric_data_binding placements_binding : references.map Prod.fst = placements.map AddressUniqueChecks.addressCode

theorem checked : CleanPlacementChecks.check capture = true := by decide +kernel

theorem placementsInBank : placements.all (fun address => decide
    (Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank.placement address) = address)) = true :=
  CleanPlacementChecks.check_sound Airbender.Compiler.FullArithmeticNative.MulDivCached.native.addresses (by decide +kernel) Airbender.Compiler.FullArithmeticNative.MulDivCached.native.addressesUnique
    placements capture bank_binding placements_binding checked

end Airbender.Compiler.CleanPlacementNative.MulDivCached
