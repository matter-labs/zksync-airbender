import Airbender.Proofs.Blake2G.FrameDefinitions

namespace Airbender.Blake2G.Proofs.FrameQueryShapes
open Arithmetic

def values0 {p : Nat} (f : Frame p) : Vector (ZMod p) 9 :=
  #v[f.dBytes[0], f.firstABytes[0], f.firstDBytes[0], 0, 0, 0, 0, 0, 4]

def values1 {p : Nat} (f : Frame p) : Vector (ZMod p) 9 :=
  #v[-7864320 * f.inputs[6] + 7864320 * f.dBytes[0], -7864320 * f.inputs[0] - 7864320 * f.inputs[2] - 7864320 * f.inputs[8] - 256 * f.addCarries[0] + 7864320 * f.firstABytes[0], f.firstDBytes[1], 0, 0, 0, 0, 0, 4]

def values2 {p : Nat} (f : Frame p) : Vector (ZMod p) 9 :=
  #v[f.dBytes[1], f.firstABytes[1], f.firstDBytes[2], 0, 0, 0, 0, 0, 4]

def values3 {p : Nat} (f : Frame p) : Vector (ZMod p) 9 :=
  #v[-7864320 * f.inputs[7] + 7864320 * f.dBytes[1], -7864320 * f.inputs[1] - 7864320 * f.inputs[3] - 7864320 * f.inputs[9] - 7864320 * f.addCarries[0] - 256 * f.addCarries[1] + 7864320 * f.firstABytes[1], f.firstDBytes[3], 0, 0, 0, 0, 0, 4]

def values4 {p : Nat} (f : Frame p) : Vector (ZMod p) 9 :=
  #v[f.bLow[0], f.cLow[0], (combinedHigh f.packedB[1]), 0, 0, 0, 0, 0, 17]

def values5 {p : Nat} (f : Frame p) : Vector (ZMod p) 9 :=
  #v[f.bMiddle[0], f.cMiddle[0], f.firstBMiddle[0], 0, 0, 0, 0, 0, 20]

def values6 {p : Nat} (f : Frame p) : Vector (ZMod p) 9 :=
  #v[-491520 * f.inputs[2] + 491520 * f.bLow[0] + 3932160 * f.bMiddle[0], -491520 * f.inputs[4] - 491520 * f.firstDBytes[2] - 125829120 * f.firstDBytes[3] - 16 * f.cCarries[0] + 491520 * f.cLow[0] + 3932160 * f.cMiddle[0], f.packedB[0] - 16 * (combinedHigh f.packedB[0]), 0, 0, 0, 0, 0, 18]

def values7 {p : Nat} (f : Frame p) : Vector (ZMod p) 9 :=
  #v[f.bLow[1], f.cLow[1], (combinedHigh f.packedB[0]), 0, 0, 0, 0, 0, 17]

def values8 {p : Nat} (f : Frame p) : Vector (ZMod p) 9 :=
  #v[f.bMiddle[1], f.cMiddle[1], f.firstBMiddle[1], 0, 0, 0, 0, 0, 20]

def values9 {p : Nat} (f : Frame p) : Vector (ZMod p) 9 :=
  #v[-491520 * f.inputs[3] + 491520 * f.bLow[1] + 3932160 * f.bMiddle[1], -491520 * f.inputs[5] - 491520 * f.firstDBytes[0] - 125829120 * f.firstDBytes[1] - 491520 * f.cCarries[0] - 16 * f.cCarries[1] + 491520 * f.cLow[1] + 3932160 * f.cMiddle[1], f.packedB[1] - 16 * (combinedHigh f.packedB[1]), 0, 0, 0, 0, 0, 18]

def values10 {p : Nat} (f : Frame p) : Vector (ZMod p) 9 :=
  #v[f.firstDBytes[2], f.secondABytes[0], f.secondDBytes[0], 0, 0, 0, 0, 0, 4]

def values11 {p : Nat} (f : Frame p) : Vector (ZMod p) 9 :=
  #v[f.firstDBytes[3], -7864320 * f.inputs[0] - 7864320 * f.inputs[2] - 7864320 * f.inputs[8] - 7864320 * f.inputs[10] - 256 * f.addCarries[0] - 7864320 * f.packedB[0] - 1006632960 * f.firstBMiddle[1] - 256 * f.addCarries[2] + 7864320 * f.secondABytes[0], f.secondDBytes[1], 0, 0, 0, 0, 0, 4]

def values12 {p : Nat} (f : Frame p) : Vector (ZMod p) 9 :=
  #v[f.firstDBytes[0], f.secondABytes[1], f.secondDBytes[2], 0, 0, 0, 0, 0, 4]

def values13 {p : Nat} (f : Frame p) : Vector (ZMod p) 9 :=
  #v[f.firstDBytes[1], -7864320 * f.inputs[1] - 7864320 * f.inputs[3] - 7864320 * f.inputs[9] - 7864320 * f.inputs[11] - 7864320 * f.addCarries[0] - 256 * f.addCarries[1] - 1006632960 * f.firstBMiddle[0] - 7864320 * f.packedB[1] - 7864320 * f.addCarries[2] - 256 * f.addCarries[3] + 7864320 * f.secondABytes[1], f.secondDBytes[3], 0, 0, 0, 0, 0, 4]

def values14 {p : Nat} (f : Frame p) : Vector (ZMod p) 9 :=
  #v[f.packedB[0], f.secondCLow[0], f.secondBChunks[0], 0, 0, 0, 0, 0, 19]

def values15 {p : Nat} (f : Frame p) : Vector (ZMod p) 9 :=
  #v[f.firstBMiddle[1], -15728640 * f.inputs[4] - 15728640 * f.firstDBytes[2] + 2 * f.firstDBytes[3] - 512 * f.cCarries[0] - 15728640 * f.secondDBytes[1] + 2 * f.secondDBytes[2] - 512 * f.cCarries[2] + 15728640 * f.secondCLow[0], f.secondBChunks[1], 0, 0, 0, 0, 0, 20]

def values16 {p : Nat} (f : Frame p) : Vector (ZMod p) 9 :=
  #v[f.packedB[1], f.secondCLow[1], f.secondBChunks[2], 0, 0, 0, 0, 0, 19]

def values17 {p : Nat} (f : Frame p) : Vector (ZMod p) 9 :=
  #v[f.firstBMiddle[0], -15728640 * f.inputs[5] - 15728640 * f.firstDBytes[0] + 2 * f.firstDBytes[1] - 15728640 * f.cCarries[0] - 512 * f.cCarries[1] + 2 * f.secondDBytes[0] - 15728640 * f.secondDBytes[3] - 15728640 * f.cCarries[2] - 512 * f.cCarries[3] + 15728640 * f.secondCLow[1], f.secondBChunks[3], 0, 0, 0, 0, 0, 20]

end Airbender.Blake2G.Proofs.FrameQueryShapes
