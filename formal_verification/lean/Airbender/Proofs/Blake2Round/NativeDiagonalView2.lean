import Airbender.Proofs.Blake2Round.NativeDiagonalSources2
import Airbender.Proofs.Blake2Round.NativeDiagonalAssignment
import Airbender.Proofs.Blake2G.FrameNormalization

namespace Airbender.Blake2Round.Proofs.NativeDiagonalView2
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

theorem query0_column {p : Nat} [Fact p.Prime]
    (w : Nat → ZMod p) (lane : Fin 6) :
    NativeLayout.queryColumn .diagonal 2 0 lane w = (source0Values w)[lane] := by
  unfold NativeLayout.queryColumn
  rw [source0_lookup]
  change ((source0 (p := p)).toArray[lane.val]!).eval (Verification.environment w) = _
  rw [getElem!_pos (source0 (p := p)).toArray lane.val
    (by rw [Vector.size_toArray]; exact lane.isLt)]
  simpa using congrArg (fun row : Vector (ZMod p) 6 => row[lane]) (source0_eval w)

theorem query2_column {p : Nat} [Fact p.Prime]
    (w : Nat → ZMod p) (lane : Fin 6) :
    NativeLayout.queryColumn .diagonal 2 2 lane w = (source2Values w)[lane] := by
  unfold NativeLayout.queryColumn
  rw [source2_lookup]
  change ((source2 (p := p)).toArray[lane.val]!).eval (Verification.environment w) = _
  rw [getElem!_pos (source2 (p := p)).toArray lane.val
    (by rw [Vector.size_toArray]; exact lane.isLt)]
  simpa using congrArg (fun row : Vector (ZMod p) 6 => row[lane]) (source2_eval w)

theorem query10_column {p : Nat} [Fact p.Prime]
    (w : Nat → ZMod p) (lane : Fin 6) :
    NativeLayout.queryColumn .diagonal 2 10 lane w = (source10Values w)[lane] := by
  unfold NativeLayout.queryColumn
  rw [source10_lookup]
  change ((source10 (p := p)).toArray[lane.val]!).eval (Verification.environment w) = _
  rw [getElem!_pos (source10 (p := p)).toArray lane.val
    (by rw [Vector.size_toArray]; exact lane.isLt)]
  simpa using congrArg (fun row : Vector (ZMod p) 6 => row[lane]) (source10_eval w)

theorem query11_column {p : Nat} [Fact p.Prime]
    (w : Nat → ZMod p) (lane : Fin 6) :
    NativeLayout.queryColumn .diagonal 2 11 lane w = (source11Values w)[lane] := by
  unfold NativeLayout.queryColumn
  rw [source11_lookup]
  change ((source11 (p := p)).toArray[lane.val]!).eval (Verification.environment w) = _
  rw [getElem!_pos (source11 (p := p)).toArray lane.val
    (by rw [Vector.size_toArray]; exact lane.isLt)]
  simpa using congrArg (fun row : Vector (ZMod p) 6 => row[lane]) (source11_eval w)

theorem query14_column {p : Nat} [Fact p.Prime]
    (w : Nat → ZMod p) (lane : Fin 6) :
    NativeLayout.queryColumn .diagonal 2 14 lane w = (source14Values w)[lane] := by
  unfold NativeLayout.queryColumn
  rw [source14_lookup]
  change ((source14 (p := p)).toArray[lane.val]!).eval (Verification.environment w) = _
  rw [getElem!_pos (source14 (p := p)).toArray lane.val
    (by rw [Vector.size_toArray]; exact lane.isLt)]
  simpa using congrArg (fun row : Vector (ZMod p) 6 => row[lane]) (source14_eval w)

theorem query15_column {p : Nat} [Fact p.Prime]
    (w : Nat → ZMod p) (lane : Fin 6) :
    NativeLayout.queryColumn .diagonal 2 15 lane w = (source15Values w)[lane] := by
  unfold NativeLayout.queryColumn
  rw [source15_lookup]
  change ((source15 (p := p)).toArray[lane.val]!).eval (Verification.environment w) = _
  rw [getElem!_pos (source15 (p := p)).toArray lane.val
    (by rw [Vector.size_toArray]; exact lane.isLt)]
  simpa using congrArg (fun row : Vector (ZMod p) 6 => row[lane]) (source15_eval w)

def frame {p : Nat} (w : Nat → ZMod p) : Blake2G.Proofs.Frame p where
  inputs := #v[w 163 + w 179 + w 232 - 65536 * w 337 + w 358 + 128 * w 357 + w 234 - 65536 * w 361, w 165 + w 181 + w 233 + w 337 - 65536 * w 339 + w 359 + 128 * w 356 + w 235 + w 361 - 65536 * w 363, w 412 + 512 * w 415, w 413 + 512 * w 414, w 186 + w 264 + 256 * w 265 - 65536 * w 268 + w 284 + 256 * w 287 - 65536 * w 289, w 187 + w 262 + 256 * w 263 + w 268 - 65536 * w 271 + w 285 + 256 * w 286 + w 289 - 65536 * w 291, w 324 + 256 * w 327, w 325 + 256 * w 326, w 248, w 249, w 250, w 251]
  addCarries := #v[w 477, w 479, 30720 * w 47 - 30720 * w 163 - 30720 * w 179 - 30720 * w 232 - 30720 * w 234 - 30720 * w 248 - 30720 * w 250 - w 337 - 3932160 * w 357 - 30720 * w 358 - w 361 - 30720 * w 412 - 15728640 * w 415 - w 477 - 3932160 * w 495 - 30720 * w 496, -943718400 * w 47 + 30720 * w 48 + 943718400 * w 163 - 30720 * w 165 + 943718400 * w 179 - 30720 * w 181 + 943718400 * w 232 - 30720 * w 233 + 943718400 * w 234 - 30720 * w 235 + 943718400 * w 248 - 30720 * w 249 + 943718400 * w 250 - 30720 * w 251 - w 339 - 3932160 * w 356 - 60 * w 357 + 943718400 * w 358 - 30720 * w 359 - w 363 + 943718400 * w 412 - 30720 * w 413 - 15728640 * w 414 - 240 * w 415 - w 479 - 3932160 * w 494 - 60 * w 495 + 943718400 * w 496 - 30720 * w 497]
  cCarries := #v[w 486, w 489, 30720 * w 71 - 30720 * w 91 - 30720 * w 186 - 30720 * w 264 - 7864320 * w 265 - w 268 - 30720 * w 284 - 7864320 * w 287 - w 289 - 30720 * w 482 - 7864320 * w 483 - w 486, -943718400 * w 71 + 30720 * w 72 + 943718400 * w 91 - 30720 * w 92 + 943718400 * w 186 - 30720 * w 187 - 30720 * w 262 - 7864320 * w 263 + 943718400 * w 264 - 120 * w 265 - w 271 + 943718400 * w 284 - 30720 * w 285 - 7864320 * w 286 - 120 * w 287 - w 291 - 30720 * w 480 - 7864320 * w 481 + 943718400 * w 482 - 120 * w 483 - w 489]
  firstABytes := #v[w 476, w 478]
  dBytes := #v[w 324, w 325]
  firstDBytes := #v[w 480, w 481, w 482, w 483]
  bLow := #v[w 490, w 492]
  bMiddle := #v[w 491, w 493]
  cLow := #v[w 484, w 487]
  cMiddle := #v[w 485, w 488]
  firstBMiddle := #v[w 494, w 495]
  packedB := #v[w 496, w 497]
  secondABytes := #v[w 498, w 499]
  secondDBytes := #v[-7864320 * w 92 + 7864320 * w 501, w 500, -7864320 * w 91 + 7864320 * w 500, w 501]
  secondCLow := #v[w 502, w 503]
  secondBChunks := #v[-3932160 * w 68 + 3932160 * w 505, w 504, -3932160 * w 67 + 3932160 * w 504, w 505]

theorem frame_eq {p : Nat} [Fact p.Prime] (w : Nat → ZMod p) :
    diagonalFrame 2 w = frame w := by
  simp only [diagonalFrame, frame, NativeLayout.Layout.read]
  congr 1
  all_goals ext lane bound
  all_goals interval_cases lane
  all_goals simp [diagonalIncoming, nativeColumnAssignment,
    Blake2G.Proofs.Frame.assignment_eq_normalized, Blake2G.Proofs.Frame.normalizedAssignment,
    columnFrame, NativeLayout.column, NativeLayout.columnInputs, NativeLayout.diagonal,
    NativeLayout.Layout.read, NativeLayout.Location.read,
    query0_column, query2_column, query10_column, query11_column, query14_column, query15_column,
    source0Values, source2Values, source10Values, source11Values, source14Values, source15Values]

end Airbender.Blake2Round.Proofs.NativeDiagonalView2
