module
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

local instance generatedBatch12Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch12Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

def native.placement (index : Nat) : Fin 301 :=
  (([(0,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerMemory 88)),
              (1,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerMemory 89)),
              (2,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerMemory 90)),
              (3,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerMemory 2)),
              (4,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerMemory 3)),
              (5,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerMemory 4)),
              (6,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerMemory 5)),
              (7,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerMemory 14)),
              (8,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerMemory 27)),
              (9,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerMemory 40)),
              (10,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerMemory 53)),
              (11,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerMemory 66)),
              (12,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerMemory 79)),
              (13,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerMemory 8)),
              (14,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerMemory 9)),
              (15,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerMemory 12)),
              (16,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerMemory 13)),
              (17,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerMemory 15)),
              (18,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerMemory 16)),
              (19,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerMemory 19)),
              (20,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerMemory 20)),
              (21,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerMemory 21)),
              (22,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerMemory 22)),
              (23,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerMemory 25)),
              (24,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerMemory 26)),
              (25,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerMemory 28)),
              (26,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerMemory 29)),
              (27,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerMemory 32)),
              (28,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerMemory 33)),
              (29,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerMemory 34)),
              (30,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerMemory 35)),
              (31,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerMemory 38)),
              (32,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerMemory 39)),
              (33,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerMemory 41)),
              (34,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerMemory 42)),
              (35,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerMemory 45)),
              (36,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerMemory 46)),
              (37,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerMemory 47)),
              (38,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerMemory 48)),
              (39,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerMemory 51)),
              (40,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerMemory 52)),
              (41,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerMemory 54)),
              (42,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerMemory 55)),
              (43,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerMemory 58)),
              (44,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerMemory 59)),
              (45,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerMemory 60)),
              (46,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerMemory 61)),
              (47,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerMemory 64)),
              (48,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerMemory 65)),
              (49,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerMemory 67)),
              (50,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerMemory 68)),
              (51,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerMemory 71)),
              (52,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerMemory 72)),
              (53,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerMemory 73)),
              (54,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerMemory 74)),
              (55,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerMemory 77)),
              (56,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerMemory 78)),
              (57,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerMemory 80)),
              (58,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerMemory 81)),
              (59,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerMemory 84)),
              (60,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerMemory 85)),
              (61,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerMemory 86)),
              (62,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerMemory 87)),
              (63,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 0)),
              (64,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 1)),
              (65,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 2)),
              (66,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 3)),
              (67,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 4)),
              (68,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 5)),
              (69,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 6)),
              (70,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 7)),
              (71,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 8)),
              (72,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 9)),
              (73,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 10)),
              (74,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 11)),
              (75,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 12)),
              (76,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 13)),
              (77,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 14)),
              (78,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 15)),
              (79,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 16)),
              (80,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 17)),
              (81,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 18)),
              (82,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 19)),
              (83,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 20)),
              (84,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 21)),
              (85,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 22)),
              (86,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 23)),
              (87,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 24)),
              (88,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 25)),
              (89,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 26)),
              (90,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 27)),
              (91,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 28)),
              (92,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 29)),
              (93,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 30)),
              (94,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 31)),
              (95,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 32)),
              (96,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 33)),
              (97,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 34)),
              (98,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 35)),
              (99,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 36)),
              (100,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 37)),
              (101,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 38)),
              (102,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 39)),
              (103,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 40)),
              (104,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 41)),
              (105,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 42)),
              (106,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 43)),
              (107,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 44)),
              (108,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 45)),
              (109,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 46)),
              (110,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 47)),
              (111,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 48)),
              (112,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 49)),
              (113,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 50)),
              (114,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 51)),
              (115,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 52)),
              (116,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 53)),
              (117,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 54)),
              (118,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 55)),
              (119,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 56)),
              (120,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 57)),
              (121,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 58)),
              (122,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 59)),
              (123,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 60)),
              (124,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 61)),
              (125,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 62)),
              (126,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 63)),
              (127,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 64)),
              (128,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 65)),
              (129,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 66)),
              (130,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 67)),
              (131,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 68)),
              (132,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 69)),
              (133,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 70)),
              (134,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 71)),
              (135,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 72)),
              (136,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 73)),
              (137,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 74)),
              (138,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 75)),
              (139,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 76)),
              (140,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 77)),
              (141,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 78)),
              (142,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 79)),
              (143,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 80)),
              (144,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 81)),
              (145,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 82)),
              (146,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 83)),
              (147,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 84)),
              (148,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 85)),
              (149,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 86)),
              (150,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 87)),
              (151,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 88)),
              (152,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 89)),
              (153,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 90)),
              (154,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 91)),
              (155,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 92)),
              (156,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 93)),
              (157,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 94)),
              (158,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 95)),
              (159,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 96)),
              (160,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 97)),
              (161,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 98)),
              (162,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 99)),
              (163,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 100)),
              (164,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 101)),
              (165,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 102)),
              (166,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 103)),
              (167,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 104)),
              (168,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 105)),
              (169,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 106)),
              (170,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 107)),
              (171,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 108)),
              (172,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 109)),
              (173,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 110)),
              (174,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 111)),
              (175,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 112)),
              (176,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 113)),
              (177,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 114)),
              (178,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 115)),
              (179,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 116)),
              (180,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 117)),
              (181,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 118)),
              (182,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 119)),
              (183,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 120)),
              (184,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 121)),
              (185,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 122)),
              (186,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 123)),
              (187,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 124)),
              (188,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 125)),
              (189,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 126)),
              (190,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 127)),
              (191,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 128)),
              (192,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 129)),
              (193,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 130)),
              (194,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 131)),
              (195,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 132)),
              (196,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 133)),
              (197,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 134)),
              (198,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 135)),
              (199,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 136)),
              (200,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 137)),
              (201,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 138)),
              (202,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 139)),
              (203,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 140)),
              (204,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 141)),
              (205,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 142)),
              (206,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 143)),
              (207,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 144)),
              (208,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 145)),
              (209,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 146)),
              (210,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 147)),
              (211,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 148)),
              (212,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 149)),
              (213,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 150)),
              (214,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 151)),
              (215,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 152)),
              (216,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 153)),
              (217,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 154)),
              (218,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 155)),
              (219,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 156)),
              (220,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 157)),
              (221,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 158)),
              (222,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerMemory 0)),
              (223,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerMemory 1)),
              (224,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 159)),
              (225,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerMemory 6)),
              (226,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerMemory 7)),
              (227,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 160)),
              (228,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerMemory 10)),
              (229,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerMemory 11)),
              (230,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 161)),
              (231,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerMemory 17)),
              (232,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerMemory 18)),
              (233,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 162)),
              (234,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerMemory 23)),
              (235,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerMemory 24)),
              (236,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 163)),
              (237,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerMemory 30)),
              (238,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerMemory 31)),
              (239,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 164)),
              (240,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerMemory 36)),
              (241,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerMemory 37)),
              (242,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 165)),
              (243,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerMemory 43)),
              (244,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerMemory 44)),
              (245,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 166)),
              (246,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerMemory 49)),
              (247,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerMemory 50)),
              (248,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 167)),
              (249,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerMemory 56)),
              (250,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerMemory 57)),
              (251,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 168)),
              (252,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerMemory 62)),
              (253,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerMemory 63)),
              (254,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 169)),
              (255,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerMemory 69)),
              (256,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerMemory 70)),
              (257,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 170)),
              (258,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerMemory 75)),
              (259,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerMemory 76)),
              (260,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 171)),
              (261,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerMemory 82)),
              (262,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerMemory 83)),
              (263,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 172)),
              (264,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 173)),
              (265,
                (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).placement
                  (GKRAddress.BaseLayerWitness 174))] :
            List (Nat × Fin 301)).lookup
        index).getD
    ⟨0, by decide⟩
end Airbender.Compiler.CleanArithmeticNative.KeccakCached
