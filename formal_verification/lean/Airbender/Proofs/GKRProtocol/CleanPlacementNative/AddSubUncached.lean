import Airbender.Proofs.GKRProtocol.CleanPlacementChecks
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport
import Airbender.Proofs.GKRProtocol.FullArithmeticNative.AddSubUncached

namespace Airbender.Compiler.CleanPlacementNative.AddSubUncached
open Airbender Airbender.Compiler NumericPolynomialChecks
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

def bankCodes0 : List Nat := [325, 362, 401, 442, 290, 17, 82, 197, 0, 1, 4, 9, 16, 25, 36, 49]
def bankCodes1 : List Nat := [64, 81, 100, 485, 530, 577, 626, 2, 3, 5, 10, 26, 37, 50, 65, 145]
def bankCodes2 : List Nat := [170, 226, 257, 101, 122, 121, 144, 169, 196, 225, 256, 289, 324, 361, 400, 441]
def bankCodes3 : List Nat := [8, 14886, 38, 160803]

def bank : LookupTable Nat := (LookupTable.branch 32 (LookupTable.branch 16 (LookupTable.leaf bankCodes0) (LookupTable.leaf bankCodes1)) (LookupTable.branch 16 (LookupTable.leaf bankCodes2) (LookupTable.leaf bankCodes3)))
def placements : List GKRAddress := [(.BaseLayerMemory 18), (.BaseLayerMemory 19), (.BaseLayerMemory 20), (.BaseLayerMemory 21), (.BaseLayerMemory 17), (.BaseLayerMemory 4), (.BaseLayerMemory 9), (.BaseLayerMemory 14), (.BaseLayerWitness 0), (.BaseLayerWitness 1), (.BaseLayerWitness 2), (.BaseLayerWitness 3), (.BaseLayerWitness 4), (.BaseLayerWitness 5), (.BaseLayerWitness 6), (.BaseLayerWitness 7), (.BaseLayerWitness 8), (.BaseLayerWitness 9), (.BaseLayerWitness 10), (.BaseLayerMemory 22), (.BaseLayerMemory 23), (.BaseLayerMemory 24), (.BaseLayerMemory 25), (.BaseLayerMemory 0), (.BaseLayerMemory 1), (.BaseLayerMemory 2), (.BaseLayerMemory 3), (.BaseLayerMemory 5), (.BaseLayerMemory 6), (.BaseLayerMemory 7), (.BaseLayerMemory 8), (.BaseLayerMemory 12), (.BaseLayerMemory 13), (.BaseLayerMemory 15), (.BaseLayerMemory 16), (.BaseLayerMemory 10), (.BaseLayerMemory 11), (.BaseLayerWitness 11), (.BaseLayerWitness 12), (.BaseLayerWitness 13), (.BaseLayerWitness 14), (.BaseLayerWitness 15), (.BaseLayerWitness 16), (.BaseLayerWitness 17), (.BaseLayerWitness 18), (.BaseLayerWitness 19), (.BaseLayerWitness 20), (.BaseLayerWitness 21)]
def references : List (Nat × Nat) := [(325, 0), (362, 1), (401, 2), (442, 3), (290, 4), (17, 5), (82, 6), (197, 7), (0, 8), (1, 9), (4, 10), (9, 11), (16, 12), (25, 13), (36, 14), (49, 15), (64, 16), (81, 17), (100, 18), (485, 19), (530, 20), (577, 21), (626, 22), (2, 23), (3, 24), (5, 25), (10, 26), (26, 27), (37, 28), (50, 29), (65, 30), (145, 31), (170, 32), (226, 33), (257, 34), (101, 35), (122, 36), (121, 37), (144, 38), (169, 39), (196, 40), (225, 41), (256, 42), (289, 43), (324, 44), (361, 45), (400, 46), (441, 47)]
def capture : CleanPlacementChecks.Capture := ⟨bank, references⟩

numeric_data_binding bank_binding : bank.toList = Airbender.Compiler.FullArithmeticNative.AddSubUncached.native.addresses.map AddressUniqueChecks.addressCode
numeric_data_binding placements_binding : references.map Prod.fst = placements.map AddressUniqueChecks.addressCode

theorem checked : CleanPlacementChecks.check capture = true := by decide +kernel

theorem placementsInBank : placements.all (fun address => decide
    (Airbender.Compiler.FullArithmeticNative.AddSubUncached.native.bank.address (Airbender.Compiler.FullArithmeticNative.AddSubUncached.native.bank.placement address) = address)) = true :=
  CleanPlacementChecks.check_sound Airbender.Compiler.FullArithmeticNative.AddSubUncached.native.addresses (by decide +kernel) Airbender.Compiler.FullArithmeticNative.AddSubUncached.native.addressesUnique
    placements capture bank_binding placements_binding checked

end Airbender.Compiler.CleanPlacementNative.AddSubUncached
