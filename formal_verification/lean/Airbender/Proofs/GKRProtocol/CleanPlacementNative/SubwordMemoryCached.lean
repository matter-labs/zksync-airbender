import Airbender.Proofs.GKRProtocol.CleanPlacementChecks
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport
import Airbender.Proofs.GKRProtocol.FullArithmeticNative.SubwordMemoryCached

namespace Airbender.Compiler.CleanPlacementNative.SubwordMemoryCached
open Airbender Airbender.Compiler NumericPolynomialChecks
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

def bankCodes0 : List Nat := [442, 485, 530, 577, 401, 17, 0, 1, 4, 9, 82, 16, 25, 626, 677, 730]
def bankCodes1 : List Nat := [785, 2, 3, 5, 10, 101, 122, 26, 37, 50, 65, 257, 290, 145, 170, 197]
def bankCodes2 : List Nat := [226, 325, 362, 36, 49, 678, 1371, 2502, 64, 81, 4227, 100, 6726, 10203, 14886, 21027]
def bankCodes3 : List Nat := [28902, 38811, 51078, 66051, 38, 84102, 105627, 51, 131046, 160803, 66, 195366, 235227, 123, 121, 144]
def bankCodes4 : List Nat := [169, 196, 225, 256, 8, 1503078, 28567, 326, 4102, 6567, 10006, 14647, 20742]

def bank : LookupTable Nat := (LookupTable.branch 32 (LookupTable.branch 16 (LookupTable.leaf bankCodes0) (LookupTable.leaf bankCodes1)) (LookupTable.branch 16 (LookupTable.leaf bankCodes2) (LookupTable.branch 16 (LookupTable.leaf bankCodes3) (LookupTable.leaf bankCodes4))))
def placements : List GKRAddress := [(.BaseLayerMemory 21), (.BaseLayerMemory 22), (.BaseLayerMemory 23), (.BaseLayerMemory 24), (.BaseLayerMemory 20), (.BaseLayerMemory 4), (.BaseLayerWitness 0), (.BaseLayerWitness 1), (.BaseLayerWitness 2), (.BaseLayerWitness 3), (.BaseLayerMemory 9), (.BaseLayerWitness 4), (.BaseLayerWitness 5), (.BaseLayerMemory 25), (.BaseLayerMemory 26), (.BaseLayerMemory 27), (.BaseLayerMemory 28), (.BaseLayerMemory 0), (.BaseLayerMemory 1), (.BaseLayerMemory 2), (.BaseLayerMemory 3), (.BaseLayerMemory 10), (.BaseLayerMemory 11), (.BaseLayerMemory 5), (.BaseLayerMemory 6), (.BaseLayerMemory 7), (.BaseLayerMemory 8), (.BaseLayerMemory 16), (.BaseLayerMemory 17), (.BaseLayerMemory 12), (.BaseLayerMemory 13), (.BaseLayerMemory 14), (.BaseLayerMemory 15), (.BaseLayerMemory 18), (.BaseLayerMemory 19), (.BaseLayerWitness 6), (.BaseLayerWitness 7), (.InnerLayer 1 5), (.InnerLayer 1 6), (.InnerLayer 1 7), (.BaseLayerWitness 8), (.BaseLayerWitness 9), (.InnerLayer 1 8), (.BaseLayerWitness 10), (.InnerLayer 1 9), (.InnerLayer 1 10), (.InnerLayer 1 11), (.InnerLayer 1 12), (.InnerLayer 1 13), (.InnerLayer 1 14), (.InnerLayer 1 15), (.InnerLayer 1 16), (.InnerLayer 2 0), (.InnerLayer 1 17), (.InnerLayer 1 18), (.InnerLayer 2 1), (.InnerLayer 1 19), (.InnerLayer 1 20), (.InnerLayer 2 2), (.InnerLayer 1 21), (.InnerLayer 1 22), (.InnerLayer 2 3), (.BaseLayerWitness 11), (.BaseLayerWitness 12), (.BaseLayerWitness 13), (.BaseLayerWitness 14), (.BaseLayerWitness 15), (.BaseLayerWitness 16)]
def references : List (Nat × Nat) := [(442, 0), (485, 1), (530, 2), (577, 3), (401, 4), (17, 5), (0, 6), (1, 7), (4, 8), (9, 9), (82, 10), (16, 11), (25, 12), (626, 13), (677, 14), (730, 15), (785, 16), (2, 17), (3, 18), (5, 19), (10, 20), (101, 21), (122, 22), (26, 23), (37, 24), (50, 25), (65, 26), (257, 27), (290, 28), (145, 29), (170, 30), (197, 31), (226, 32), (325, 33), (362, 34), (36, 35), (49, 36), (678, 37), (1371, 38), (2502, 39), (64, 40), (81, 41), (4227, 42), (100, 43), (6726, 44), (10203, 45), (14886, 46), (21027, 47), (28902, 48), (38811, 49), (51078, 50), (66051, 51), (38, 52), (84102, 53), (105627, 54), (51, 55), (131046, 56), (160803, 57), (66, 58), (195366, 59), (235227, 60), (123, 61), (121, 62), (144, 63), (169, 64), (196, 65), (225, 66), (256, 67)]
def capture : CleanPlacementChecks.Capture := ⟨bank, references⟩

numeric_data_binding bank_binding : bank.toList = Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.addresses.map AddressUniqueChecks.addressCode
numeric_data_binding placements_binding : references.map Prod.fst = placements.map AddressUniqueChecks.addressCode

theorem checked : CleanPlacementChecks.check capture = true := by decide +kernel

theorem placementsInBank : placements.all (fun address => decide
    (Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.bank.placement address) = address)) = true :=
  CleanPlacementChecks.check_sound Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.addresses (by decide +kernel) Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.addressesUnique
    placements capture bank_binding placements_binding checked

end Airbender.Compiler.CleanPlacementNative.SubwordMemoryCached
