module
import all Mathlib.Data.List.Sort
public import Proven.GKRProtocol.CleanPlacementChecks
public import Proven.Import.GKRProtocol.NumericArithmeticDataImport
public import Proven.GKRProtocol.FullArithmeticNative.BlakeGCached

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.CleanPlacementNative.BlakeGCached
open Airbender Airbender.Compiler NumericPolynomialChecks
set_option maxRecDepth 32768

def bankCodes0 : List Nat := [2705, 2810, 2917, 2305, 2402, 2501, 2602, 65, 226, 485, 842, 1601, 2026, 5, 10, 37]
def bankCodes1 : List Nat := [50, 82, 101, 170, 197, 257, 290, 401, 442, 530, 577, 730, 785, 901, 962, 1157]
def bankCodes2 : List Nat := [1226, 1445, 1522, 1850, 1937, 0, 1, 4, 9, 16, 25, 36, 49, 64, 81, 100]
def bankCodes3 : List Nat := [121, 144, 169, 196, 225, 256, 289, 324, 361, 400, 441, 484, 529, 576, 625, 676]
def bankCodes4 : List Nat := [729, 784, 841, 900, 961, 1024, 1089, 1156, 1225, 1296, 1369, 1444, 1521, 1600, 1681, 1764]
def bankCodes5 : List Nat := [1849, 1936, 2025, 2116, 2209, 2304, 2401, 2500, 2601, 2704, 2809, 2916, 3025, 3136, 2, 3]
def bankCodes6 : List Nat := [17, 26, 122, 145, 325, 362, 626, 677, 1025, 1090, 1297, 1370, 1682, 1765, 2117, 2210]
def bankCodes7 : List Nat := [8, 38, 146, 402, 160006, 194487, 234262, 279847, 331782, 390631, 456982, 531447, 614662, 707287, 810006, 923527]
def bankCodes8 : List Nat := [1048582, 1185927, 1336342, 1500631, 1679622, 1874167, 2085142, 2313447, 2560006]

def bank : LookupTable Nat := (LookupTable.branch 64 (LookupTable.branch 32 (LookupTable.branch 16 (LookupTable.leaf bankCodes0) (LookupTable.leaf bankCodes1)) (LookupTable.branch 16 (LookupTable.leaf bankCodes2) (LookupTable.leaf bankCodes3))) (LookupTable.branch 32 (LookupTable.branch 16 (LookupTable.leaf bankCodes4) (LookupTable.leaf bankCodes5)) (LookupTable.branch 16 (LookupTable.leaf bankCodes6) (LookupTable.branch 16 (LookupTable.leaf bankCodes7) (LookupTable.leaf bankCodes8)))))
def placements : List GKRAddress := [(.BaseLayerMemory 52), (.BaseLayerMemory 53), (.BaseLayerMemory 54), (.BaseLayerMemory 48), (.BaseLayerMemory 49), (.BaseLayerMemory 50), (.BaseLayerMemory 51), (.BaseLayerMemory 8), (.BaseLayerMemory 15), (.BaseLayerMemory 22), (.BaseLayerMemory 29), (.BaseLayerMemory 40), (.BaseLayerMemory 45), (.BaseLayerMemory 2), (.BaseLayerMemory 3), (.BaseLayerMemory 6), (.BaseLayerMemory 7), (.BaseLayerMemory 9), (.BaseLayerMemory 10), (.BaseLayerMemory 13), (.BaseLayerMemory 14), (.BaseLayerMemory 16), (.BaseLayerMemory 17), (.BaseLayerMemory 20), (.BaseLayerMemory 21), (.BaseLayerMemory 23), (.BaseLayerMemory 24), (.BaseLayerMemory 27), (.BaseLayerMemory 28), (.BaseLayerMemory 30), (.BaseLayerMemory 31), (.BaseLayerMemory 34), (.BaseLayerMemory 35), (.BaseLayerMemory 38), (.BaseLayerMemory 39), (.BaseLayerMemory 43), (.BaseLayerMemory 44), (.BaseLayerWitness 0), (.BaseLayerWitness 1), (.BaseLayerWitness 2), (.BaseLayerWitness 3), (.BaseLayerWitness 4), (.BaseLayerWitness 5), (.BaseLayerWitness 6), (.BaseLayerWitness 7), (.BaseLayerWitness 8), (.BaseLayerWitness 9), (.BaseLayerWitness 10), (.BaseLayerWitness 11), (.BaseLayerWitness 12), (.BaseLayerWitness 13), (.BaseLayerWitness 14), (.BaseLayerWitness 15), (.BaseLayerWitness 16), (.BaseLayerWitness 17), (.BaseLayerWitness 18), (.BaseLayerWitness 19), (.BaseLayerWitness 20), (.BaseLayerWitness 21), (.BaseLayerWitness 22), (.BaseLayerWitness 23), (.BaseLayerWitness 24), (.BaseLayerWitness 25), (.BaseLayerWitness 26), (.BaseLayerWitness 27), (.BaseLayerWitness 28), (.BaseLayerWitness 29), (.BaseLayerWitness 30), (.BaseLayerWitness 31), (.BaseLayerWitness 32), (.BaseLayerWitness 33), (.BaseLayerWitness 34), (.BaseLayerWitness 35), (.BaseLayerWitness 36), (.BaseLayerWitness 37), (.BaseLayerWitness 38), (.BaseLayerWitness 39), (.BaseLayerWitness 40), (.BaseLayerWitness 41), (.BaseLayerWitness 42), (.BaseLayerWitness 43), (.BaseLayerWitness 44), (.BaseLayerWitness 45), (.BaseLayerMemory 0), (.BaseLayerMemory 1), (.BaseLayerWitness 46), (.BaseLayerMemory 4), (.BaseLayerMemory 5), (.BaseLayerWitness 47), (.BaseLayerMemory 11), (.BaseLayerMemory 12), (.BaseLayerWitness 48), (.BaseLayerMemory 18), (.BaseLayerMemory 19), (.BaseLayerWitness 49), (.BaseLayerMemory 25), (.BaseLayerMemory 26), (.BaseLayerWitness 50), (.BaseLayerMemory 32), (.BaseLayerMemory 33), (.BaseLayerWitness 51), (.BaseLayerMemory 36), (.BaseLayerMemory 37), (.BaseLayerWitness 52), (.BaseLayerMemory 41), (.BaseLayerMemory 42), (.BaseLayerWitness 53), (.BaseLayerMemory 46), (.BaseLayerMemory 47), (.BaseLayerWitness 54), (.BaseLayerWitness 55), (.BaseLayerWitness 56)]
def references : List (Nat × Nat) := [(2705, 0), (2810, 1), (2917, 2), (2305, 3), (2402, 4), (2501, 5), (2602, 6), (65, 7), (226, 8), (485, 9), (842, 10), (1601, 11), (2026, 12), (5, 13), (10, 14), (37, 15), (50, 16), (82, 17), (101, 18), (170, 19), (197, 20), (257, 21), (290, 22), (401, 23), (442, 24), (530, 25), (577, 26), (730, 27), (785, 28), (901, 29), (962, 30), (1157, 31), (1226, 32), (1445, 33), (1522, 34), (1850, 35), (1937, 36), (0, 37), (1, 38), (4, 39), (9, 40), (16, 41), (25, 42), (36, 43), (49, 44), (64, 45), (81, 46), (100, 47), (121, 48), (144, 49), (169, 50), (196, 51), (225, 52), (256, 53), (289, 54), (324, 55), (361, 56), (400, 57), (441, 58), (484, 59), (529, 60), (576, 61), (625, 62), (676, 63), (729, 64), (784, 65), (841, 66), (900, 67), (961, 68), (1024, 69), (1089, 70), (1156, 71), (1225, 72), (1296, 73), (1369, 74), (1444, 75), (1521, 76), (1600, 77), (1681, 78), (1764, 79), (1849, 80), (1936, 81), (2025, 82), (2, 94), (3, 95), (2116, 83), (17, 96), (26, 97), (2209, 84), (122, 98), (145, 99), (2304, 85), (325, 100), (362, 101), (2401, 86), (626, 102), (677, 103), (2500, 87), (1025, 104), (1090, 105), (2601, 88), (1297, 106), (1370, 107), (2704, 89), (1682, 108), (1765, 109), (2809, 90), (2117, 110), (2210, 111), (2916, 91), (3025, 92), (3136, 93)]
def capture : CleanPlacementChecks.Capture := ⟨bank, references⟩

numeric_data_binding bank_binding : bank.toList = Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.addresses.map AddressUniqueChecks.addressCode
numeric_data_binding placements_binding : references.map Prod.fst = placements.map AddressUniqueChecks.addressCode

theorem checked : CleanPlacementChecks.check capture = true := by decide +kernel

theorem placementsInBank : placements.all (fun address => decide
    (Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank.placement address) = address)) = true :=
  CleanPlacementChecks.check_sound Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.addresses (by decide +kernel) Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.addressesUnique
    placements capture bank_binding placements_binding checked

end Airbender.Compiler.CleanPlacementNative.BlakeGCached
