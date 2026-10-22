import Airbender.Proofs.Blake2Round.NativeColumnSources3
import Airbender.Proofs.Blake2Round.NativeDiagonalAssignment
import Airbender.Proofs.Blake2G.FrameNormalization

namespace Airbender.Blake2Round.Proofs.NativeColumnView3
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

def frame {p : Nat} (w : Nat → ZMod p) : Blake2G.Proofs.Frame p where
  inputs := #v[w 167, w 169, w 183, w 185, w 192, w 193, w 196, w 197, w 236, w 237, w 238, w 239]
  addCarries := #v[w 377, w 379, w 401, w 403]
  cCarries := #v[w 388, w 391, w 409, w 411]
  firstABytes := #v[w 376, w 378]
  dBytes := #v[w 380, w 381]
  firstDBytes := #v[w 382, w 383, w 384, w 385]
  bLow := #v[w 392, w 394]
  bMiddle := #v[w 393, w 395]
  cLow := #v[w 386, w 389]
  cMiddle := #v[w 387, w 390]
  firstBMiddle := #v[w 396, w 397]
  packedB := #v[w 398, w 399]
  secondABytes := #v[w 400, w 402]
  secondDBytes := #v[w 406, w 404, w 407, w 405]
  secondCLow := #v[w 408, w 410]
  secondBChunks := #v[w 414, w 412, w 415, w 413]

theorem frame_eq {p : Nat} [Fact p.Prime] (w : Nat → ZMod p) :
    columnFrame 3 w = frame w := by
  simp [columnFrame, frame, NativeLayout.column, NativeLayout.Layout.read,
    NativeLayout.Location.read, NativeLayout.columnInputs]

end Airbender.Blake2Round.Proofs.NativeColumnView3
