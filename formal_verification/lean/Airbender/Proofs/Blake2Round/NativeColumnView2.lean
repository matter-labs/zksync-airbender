import Airbender.Proofs.Blake2Round.NativeColumnSources2
import Airbender.Proofs.Blake2Round.NativeDiagonalAssignment
import Airbender.Proofs.Blake2G.FrameNormalization

namespace Airbender.Blake2Round.Proofs.NativeColumnView2
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

def frame {p : Nat} (w : Nat → ZMod p) : Blake2G.Proofs.Frame p where
  inputs := #v[w 163, w 165, w 179, w 181, w 190, w 191, w 200, w 201, w 232, w 233, w 234, w 235]
  addCarries := #v[w 337, w 339, w 361, w 363]
  cCarries := #v[w 348, w 351, w 369, w 371]
  firstABytes := #v[w 336, w 338]
  dBytes := #v[w 340, w 341]
  firstDBytes := #v[w 342, w 343, w 344, w 345]
  bLow := #v[w 352, w 354]
  bMiddle := #v[w 353, w 355]
  cLow := #v[w 346, w 349]
  cMiddle := #v[w 347, w 350]
  firstBMiddle := #v[w 356, w 357]
  packedB := #v[w 358, w 359]
  secondABytes := #v[w 360, w 362]
  secondDBytes := #v[w 366, w 364, w 367, w 365]
  secondCLow := #v[w 368, w 370]
  secondBChunks := #v[w 374, w 372, w 375, w 373]

theorem frame_eq {p : Nat} [Fact p.Prime] (w : Nat → ZMod p) :
    columnFrame 2 w = frame w := by
  simp [columnFrame, frame, NativeLayout.column, NativeLayout.Layout.read,
    NativeLayout.Location.read, NativeLayout.columnInputs]

end Airbender.Blake2Round.Proofs.NativeColumnView2
