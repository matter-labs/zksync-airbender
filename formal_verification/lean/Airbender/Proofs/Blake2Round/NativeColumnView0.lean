import Airbender.Proofs.Blake2Round.NativeColumnSources0
import Airbender.Proofs.Blake2Round.NativeDiagonalAssignment
import Airbender.Proofs.Blake2G.FrameNormalization

namespace Airbender.Blake2Round.Proofs.NativeColumnView0
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

def frame {p : Nat} (w : Nat → ZMod p) : Blake2G.Proofs.Frame p where
  inputs := #v[w 155, w 157, w 171, w 173, w 186, w 187, w 198, w 199, w 224, w 225, w 226, w 227]
  addCarries := #v[w 257, w 259, w 281, w 283]
  cCarries := #v[w 268, w 271, w 289, w 291]
  firstABytes := #v[w 256, w 258]
  dBytes := #v[w 260, w 261]
  firstDBytes := #v[w 262, w 263, w 264, w 265]
  bLow := #v[w 272, w 274]
  bMiddle := #v[w 273, w 275]
  cLow := #v[w 266, w 269]
  cMiddle := #v[w 267, w 270]
  firstBMiddle := #v[w 276, w 277]
  packedB := #v[w 278, w 279]
  secondABytes := #v[w 280, w 282]
  secondDBytes := #v[w 286, w 284, w 287, w 285]
  secondCLow := #v[w 288, w 290]
  secondBChunks := #v[w 294, w 292, w 295, w 293]

theorem frame_eq {p : Nat} [Fact p.Prime] (w : Nat → ZMod p) :
    columnFrame 0 w = frame w := by
  simp [columnFrame, frame, NativeLayout.column, NativeLayout.Layout.read,
    NativeLayout.Location.read, NativeLayout.columnInputs]

end Airbender.Blake2Round.Proofs.NativeColumnView0
