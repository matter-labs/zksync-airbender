import Airbender.Proofs.GKRProtocol.CleanPlacementChecks
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport
import Airbender.Proofs.GKRProtocol.FullArithmeticNative.WordMemoryCached

namespace Airbender.Compiler.CleanPlacementNative.WordMemoryCached
open Airbender Airbender.Compiler NumericPolynomialChecks
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

def bankCodes0 : List Nat := [442, 485, 530, 577, 401, 17, 0, 1, 4, 9, 82, 626, 677, 730, 785, 2]
def bankCodes1 : List Nat := [3, 5, 10, 101, 122, 26, 37, 50, 65, 257, 290, 145, 170, 197, 226, 325]
def bankCodes2 : List Nat := [362, 678, 1371, 16, 2502, 4227, 6726, 38, 10203, 51, 14886, 66, 21027, 123, 25, 36]
def bankCodes3 : List Nat := [49, 64, 81, 100, 8, 51078, 332931, 28567, 326, 6891, 4102, 6567, 10006, 14647, 20742]

def bank : LookupTable Nat := (LookupTable.branch 32 (LookupTable.branch 16 (LookupTable.leaf bankCodes0) (LookupTable.leaf bankCodes1)) (LookupTable.branch 16 (LookupTable.leaf bankCodes2) (LookupTable.leaf bankCodes3)))
def placements : List GKRAddress := [(.BaseLayerMemory 21), (.BaseLayerMemory 22), (.BaseLayerMemory 23), (.BaseLayerMemory 24), (.BaseLayerMemory 20), (.BaseLayerMemory 4), (.BaseLayerWitness 0), (.BaseLayerWitness 1), (.BaseLayerWitness 2), (.BaseLayerWitness 3), (.BaseLayerMemory 9), (.BaseLayerMemory 25), (.BaseLayerMemory 26), (.BaseLayerMemory 27), (.BaseLayerMemory 28), (.BaseLayerMemory 0), (.BaseLayerMemory 1), (.BaseLayerMemory 2), (.BaseLayerMemory 3), (.BaseLayerMemory 10), (.BaseLayerMemory 11), (.BaseLayerMemory 5), (.BaseLayerMemory 6), (.BaseLayerMemory 7), (.BaseLayerMemory 8), (.BaseLayerMemory 16), (.BaseLayerMemory 17), (.BaseLayerMemory 12), (.BaseLayerMemory 13), (.BaseLayerMemory 14), (.BaseLayerMemory 15), (.BaseLayerMemory 18), (.BaseLayerMemory 19), (.InnerLayer 1 5), (.InnerLayer 1 6), (.BaseLayerWitness 4), (.InnerLayer 1 7), (.InnerLayer 1 8), (.InnerLayer 1 9), (.InnerLayer 2 0), (.InnerLayer 1 10), (.InnerLayer 2 1), (.InnerLayer 1 11), (.InnerLayer 2 2), (.InnerLayer 1 12), (.InnerLayer 2 3), (.BaseLayerWitness 5), (.BaseLayerWitness 6), (.BaseLayerWitness 7), (.BaseLayerWitness 8), (.BaseLayerWitness 9), (.BaseLayerWitness 10)]
def references : List (Nat × Nat) := [(442, 0), (485, 1), (530, 2), (577, 3), (401, 4), (17, 5), (0, 6), (1, 7), (4, 8), (9, 9), (82, 10), (626, 11), (677, 12), (730, 13), (785, 14), (2, 15), (3, 16), (5, 17), (10, 18), (101, 19), (122, 20), (26, 21), (37, 22), (50, 23), (65, 24), (257, 25), (290, 26), (145, 27), (170, 28), (197, 29), (226, 30), (325, 31), (362, 32), (678, 33), (1371, 34), (16, 35), (2502, 36), (4227, 37), (6726, 38), (38, 39), (10203, 40), (51, 41), (14886, 42), (66, 43), (21027, 44), (123, 45), (25, 46), (36, 47), (49, 48), (64, 49), (81, 50), (100, 51)]
def capture : CleanPlacementChecks.Capture := ⟨bank, references⟩

numeric_data_binding bank_binding : bank.toList = Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.addresses.map AddressUniqueChecks.addressCode
numeric_data_binding placements_binding : references.map Prod.fst = placements.map AddressUniqueChecks.addressCode

theorem checked : CleanPlacementChecks.check capture = true := by decide +kernel

theorem placementsInBank : placements.all (fun address => decide
    (Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.bank.placement address) = address)) = true :=
  CleanPlacementChecks.check_sound Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.addresses (by decide +kernel) Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.addressesUnique
    placements capture bank_binding placements_binding checked

end Airbender.Compiler.CleanPlacementNative.WordMemoryCached
