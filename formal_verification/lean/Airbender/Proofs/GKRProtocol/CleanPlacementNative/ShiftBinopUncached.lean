import Airbender.Proofs.GKRProtocol.CleanPlacementChecks
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport
import Airbender.Proofs.GKRProtocol.FullArithmeticNative.ShiftBinopUncached

namespace Airbender.Compiler.CleanPlacementNative.ShiftBinopUncached
open Airbender Airbender.Compiler NumericPolynomialChecks
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

def bankCodes0 : List Nat := [485, 530, 577, 626, 442, 37, 170, 325, 0, 1, 4, 9, 16, 677, 730, 785]
def bankCodes1 : List Nat := [842, 2, 3, 5, 10, 17, 26, 50, 65, 82, 101, 122, 145, 257, 290, 362]
def bankCodes2 : List Nat := [401, 197, 226, 25, 36, 49, 64, 81, 100, 121, 144, 169, 196, 225, 256, 289]
def bankCodes3 : List Nat := [324, 361, 400, 441, 678, 1371, 2502, 4227, 6726, 10203, 14886, 21027, 28902, 38811, 51078, 66051]
def bankCodes4 : List Nat := [84102, 105627, 131046, 160803, 195366, 235227, 280902, 332931, 391878, 458331, 532902, 616227, 708966, 811803, 925446, 1050627]
def bankCodes5 : List Nat := [1188102, 1338651, 1503078, 1682211, 1876902, 2088027, 2316486, 2563203, 2829126, 3115227, 3422502, 3751971, 484, 529, 576, 625]
def bankCodes6 : List Nat := [676, 729, 8, 4884102, 38, 9840771]

def bank : LookupTable Nat := (LookupTable.branch 48 (LookupTable.branch 16 (LookupTable.leaf bankCodes0) (LookupTable.branch 16 (LookupTable.leaf bankCodes1) (LookupTable.leaf bankCodes2))) (LookupTable.branch 32 (LookupTable.branch 16 (LookupTable.leaf bankCodes3) (LookupTable.leaf bankCodes4)) (LookupTable.branch 16 (LookupTable.leaf bankCodes5) (LookupTable.leaf bankCodes6))))
def placements : List GKRAddress := [(.BaseLayerMemory 22), (.BaseLayerMemory 23), (.BaseLayerMemory 24), (.BaseLayerMemory 25), (.BaseLayerMemory 21), (.BaseLayerMemory 6), (.BaseLayerMemory 13), (.BaseLayerMemory 18), (.BaseLayerWitness 0), (.BaseLayerWitness 1), (.BaseLayerWitness 2), (.BaseLayerWitness 3), (.BaseLayerWitness 4), (.BaseLayerMemory 26), (.BaseLayerMemory 27), (.BaseLayerMemory 28), (.BaseLayerMemory 29), (.BaseLayerMemory 0), (.BaseLayerMemory 1), (.BaseLayerMemory 2), (.BaseLayerMemory 3), (.BaseLayerMemory 4), (.BaseLayerMemory 5), (.BaseLayerMemory 7), (.BaseLayerMemory 8), (.BaseLayerMemory 9), (.BaseLayerMemory 10), (.BaseLayerMemory 11), (.BaseLayerMemory 12), (.BaseLayerMemory 16), (.BaseLayerMemory 17), (.BaseLayerMemory 19), (.BaseLayerMemory 20), (.BaseLayerMemory 14), (.BaseLayerMemory 15), (.BaseLayerWitness 5), (.BaseLayerWitness 6), (.BaseLayerWitness 7), (.BaseLayerWitness 8), (.BaseLayerWitness 9), (.BaseLayerWitness 10), (.BaseLayerWitness 11), (.BaseLayerWitness 12), (.BaseLayerWitness 13), (.BaseLayerWitness 14), (.BaseLayerWitness 15), (.BaseLayerWitness 16), (.BaseLayerWitness 17), (.BaseLayerWitness 18), (.BaseLayerWitness 19), (.BaseLayerWitness 20), (.BaseLayerWitness 21), (.InnerLayer 1 5), (.InnerLayer 1 6), (.InnerLayer 1 7), (.InnerLayer 1 8), (.InnerLayer 1 9), (.InnerLayer 1 10), (.InnerLayer 1 11), (.InnerLayer 1 12), (.InnerLayer 1 13), (.InnerLayer 1 14), (.InnerLayer 1 15), (.InnerLayer 1 16), (.InnerLayer 1 17), (.InnerLayer 1 18), (.InnerLayer 1 19), (.InnerLayer 1 20), (.InnerLayer 1 21), (.InnerLayer 1 22), (.InnerLayer 1 23), (.InnerLayer 1 24), (.InnerLayer 1 25), (.InnerLayer 1 26), (.InnerLayer 1 27), (.InnerLayer 1 28), (.InnerLayer 1 29), (.InnerLayer 1 30), (.InnerLayer 1 31), (.InnerLayer 1 32), (.InnerLayer 1 33), (.InnerLayer 1 34), (.InnerLayer 1 35), (.InnerLayer 1 36), (.InnerLayer 1 37), (.InnerLayer 1 38), (.InnerLayer 1 39), (.InnerLayer 1 40), (.InnerLayer 1 41), (.InnerLayer 1 42), (.InnerLayer 1 43), (.InnerLayer 1 44), (.BaseLayerWitness 22), (.BaseLayerWitness 23), (.BaseLayerWitness 24), (.BaseLayerWitness 25), (.BaseLayerWitness 26), (.BaseLayerWitness 27)]
def references : List (Nat × Nat) := [(485, 0), (530, 1), (577, 2), (626, 3), (442, 4), (37, 5), (170, 6), (325, 7), (0, 8), (1, 9), (4, 10), (9, 11), (16, 12), (677, 13), (730, 14), (785, 15), (842, 16), (2, 17), (3, 18), (5, 19), (10, 20), (17, 21), (26, 22), (50, 23), (65, 24), (82, 25), (101, 26), (122, 27), (145, 28), (257, 29), (290, 30), (362, 31), (401, 32), (197, 33), (226, 34), (25, 35), (36, 36), (49, 37), (64, 38), (81, 39), (100, 40), (121, 41), (144, 42), (169, 43), (196, 44), (225, 45), (256, 46), (289, 47), (324, 48), (361, 49), (400, 50), (441, 51), (678, 52), (1371, 53), (2502, 54), (4227, 55), (6726, 56), (10203, 57), (14886, 58), (21027, 59), (28902, 60), (38811, 61), (51078, 62), (66051, 63), (84102, 64), (105627, 65), (131046, 66), (160803, 67), (195366, 68), (235227, 69), (280902, 70), (332931, 71), (391878, 72), (458331, 73), (532902, 74), (616227, 75), (708966, 76), (811803, 77), (925446, 78), (1050627, 79), (1188102, 80), (1338651, 81), (1503078, 82), (1682211, 83), (1876902, 84), (2088027, 85), (2316486, 86), (2563203, 87), (2829126, 88), (3115227, 89), (3422502, 90), (3751971, 91), (484, 92), (529, 93), (576, 94), (625, 95), (676, 96), (729, 97)]
def capture : CleanPlacementChecks.Capture := ⟨bank, references⟩

numeric_data_binding bank_binding : bank.toList = Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.addresses.map AddressUniqueChecks.addressCode
numeric_data_binding placements_binding : references.map Prod.fst = placements.map AddressUniqueChecks.addressCode

theorem checked : CleanPlacementChecks.check capture = true := by decide +kernel

theorem placementsInBank : placements.all (fun address => decide
    (Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank.address (Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank.placement address) = address)) = true :=
  CleanPlacementChecks.check_sound Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.addresses (by decide +kernel) Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.addressesUnique
    placements capture bank_binding placements_binding checked

end Airbender.Compiler.CleanPlacementNative.ShiftBinopUncached
