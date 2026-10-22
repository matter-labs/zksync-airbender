import Airbender.Proofs.Arithmetic.FieldSliceDefinitions
import Airbender.Proofs.Blake2G.AssemblyDefinitions

namespace Airbender.Blake2G.Proofs
open Arithmetic

/-- Stable arithmetic wires for one G call. These names describe arithmetic
    roles; no native column, setup offset, or query position occurs here. -/
structure Frame (p : Nat) where
  inputs : Vector (ZMod p) 12
  addCarries : Vector (ZMod p) 4
  cCarries : Vector (ZMod p) 4
  firstABytes : Vector (ZMod p) 2
  dBytes : Vector (ZMod p) 2
  firstDBytes : Vector (ZMod p) 4
  bLow : Vector (ZMod p) 2
  bMiddle : Vector (ZMod p) 2
  cLow : Vector (ZMod p) 2
  cMiddle : Vector (ZMod p) 2
  firstBMiddle : Vector (ZMod p) 2
  packedB : Vector (ZMod p) 2
  secondABytes : Vector (ZMod p) 2
  secondDBytes : Vector (ZMod p) 4
  secondCLow : Vector (ZMod p) 2
  secondBChunks : Vector (ZMod p) 4

/-- Adapt named arithmetic wires to the already checked G fragment. The numeric
    names here belong to that fixed fragment, independently of a caller layout. -/
def Frame.base {p : Nat} (frame : Frame p) (column : Nat) : ZMod p :=
  match column with
  | 15 => frame.inputs[0]
  | 16 => frame.inputs[1]
  | 19 => frame.inputs[2]
  | 20 => frame.inputs[3]
  | 23 => frame.inputs[4]
  | 24 => frame.inputs[5]
  | 27 => frame.inputs[6]
  | 28 => frame.inputs[7]
  | 33 => frame.inputs[8]
  | 34 => frame.inputs[9]
  | 35 => frame.inputs[10]
  | 36 => frame.inputs[11]
  | 37 => carryLow frame.addCarries[0]
  | 38 => carryHigh frame.addCarries[0]
  | 39 => carryLow frame.addCarries[1]
  | 40 => carryHigh frame.addCarries[1]
  | 41 => frame.firstABytes[0]
  | 42 => frame.firstABytes[1]
  | 43 => frame.dBytes[0]
  | 44 => frame.firstDBytes[0]
  | 45 => frame.firstDBytes[1]
  | 46 => frame.dBytes[1]
  | 47 => frame.firstDBytes[2]
  | 48 => frame.firstDBytes[3]
  | 49 => frame.cCarries[0]
  | 50 => frame.cCarries[1]
  | 51 => frame.cLow[0]
  | 52 => frame.cMiddle[0]
  | 53 => frame.cLow[1]
  | 54 => frame.cMiddle[1]
  | 55 => frame.bLow[0]
  | 56 => frame.bMiddle[0]
  | 57 => combinedHigh frame.packedB[1]
  | 58 => frame.firstBMiddle[0]
  | 59 => combinedLow frame.packedB[0]
  | 60 => frame.bLow[1]
  | 61 => frame.bMiddle[1]
  | 62 => combinedHigh frame.packedB[0]
  | 63 => frame.firstBMiddle[1]
  | 64 => combinedLow frame.packedB[1]
  | 65 => carryLow frame.addCarries[2]
  | 66 => carryHigh frame.addCarries[2]
  | 67 => carryLow frame.addCarries[3]
  | 68 => carryHigh frame.addCarries[3]
  | 69 => frame.secondABytes[0]
  | 70 => frame.secondABytes[1]
  | 71 => frame.secondDBytes[0]
  | 72 => frame.secondDBytes[1]
  | 73 => frame.secondDBytes[2]
  | 74 => frame.secondDBytes[3]
  | 75 => frame.cCarries[2]
  | 76 => frame.cCarries[3]
  | 77 => frame.secondCLow[0]
  | 78 => frame.secondCLow[1]
  | 79 => frame.secondBChunks[0]
  | 80 => frame.secondBChunks[1]
  | 81 => frame.secondBChunks[2]
  | 82 => frame.secondBChunks[3]
  | _ => 0

def Frame.assignment {p : Nat} (frame : Frame p) : Nat → ZMod p :=
  assemble frame.base

end Airbender.Blake2G.Proofs
