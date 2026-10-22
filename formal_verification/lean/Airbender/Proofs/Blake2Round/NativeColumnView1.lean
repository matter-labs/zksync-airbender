import Airbender.Proofs.Blake2Round.NativeColumnSources1
import Airbender.Proofs.Blake2Round.NativeDiagonalAssignment
import Airbender.Proofs.Blake2G.FrameNormalization

namespace Airbender.Blake2Round.Proofs.NativeColumnView1
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

def frame {p : Nat} (w : Nat → ZMod p) : Blake2G.Proofs.Frame p where
  inputs := #v[w 159, w 161, w 175, w 177, w 188, w 189, w 194, w 195, w 228, w 229, w 230, w 231]
  addCarries := #v[w 297, w 299, w 321, w 323]
  cCarries := #v[w 308, w 311, w 329, w 331]
  firstABytes := #v[w 296, w 298]
  dBytes := #v[w 300, w 301]
  firstDBytes := #v[w 302, w 303, w 304, w 305]
  bLow := #v[w 312, w 314]
  bMiddle := #v[w 313, w 315]
  cLow := #v[w 306, w 309]
  cMiddle := #v[w 307, w 310]
  firstBMiddle := #v[w 316, w 317]
  packedB := #v[w 318, w 319]
  secondABytes := #v[w 320, w 322]
  secondDBytes := #v[w 326, w 324, w 327, w 325]
  secondCLow := #v[w 328, w 330]
  secondBChunks := #v[w 334, w 332, w 335, w 333]

theorem frame_eq {p : Nat} [Fact p.Prime] (w : Nat → ZMod p) :
    columnFrame 1 w = frame w := by
  simp [columnFrame, frame, NativeLayout.column, NativeLayout.Layout.read,
    NativeLayout.Location.read, NativeLayout.columnInputs]

end Airbender.Blake2Round.Proofs.NativeColumnView1
