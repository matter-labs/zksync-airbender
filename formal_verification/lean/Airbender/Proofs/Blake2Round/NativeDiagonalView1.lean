import Airbender.Proofs.Blake2Round.NativeDiagonalSources1
import Airbender.Proofs.Blake2Round.NativeDiagonalAssignment
import Airbender.Proofs.Blake2G.FrameNormalization

namespace Airbender.Blake2Round.Proofs.NativeDiagonalView1
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

theorem query0_column {p : Nat} [Fact p.Prime]
    (w : Nat → ZMod p) (lane : Fin 6) :
    NativeLayout.queryColumn .diagonal 1 0 lane w = (source0Values w)[lane] := by
  unfold NativeLayout.queryColumn
  rw [source0_lookup]
  change ((source0 (p := p)).toArray[lane.val]!).eval (Verification.environment w) = _
  rw [getElem!_pos (source0 (p := p)).toArray lane.val
    (by rw [Vector.size_toArray]; exact lane.isLt)]
  simpa using congrArg (fun row : Vector (ZMod p) 6 => row[lane]) (source0_eval w)

theorem query2_column {p : Nat} [Fact p.Prime]
    (w : Nat → ZMod p) (lane : Fin 6) :
    NativeLayout.queryColumn .diagonal 1 2 lane w = (source2Values w)[lane] := by
  unfold NativeLayout.queryColumn
  rw [source2_lookup]
  change ((source2 (p := p)).toArray[lane.val]!).eval (Verification.environment w) = _
  rw [getElem!_pos (source2 (p := p)).toArray lane.val
    (by rw [Vector.size_toArray]; exact lane.isLt)]
  simpa using congrArg (fun row : Vector (ZMod p) 6 => row[lane]) (source2_eval w)

theorem query10_column {p : Nat} [Fact p.Prime]
    (w : Nat → ZMod p) (lane : Fin 6) :
    NativeLayout.queryColumn .diagonal 1 10 lane w = (source10Values w)[lane] := by
  unfold NativeLayout.queryColumn
  rw [source10_lookup]
  change ((source10 (p := p)).toArray[lane.val]!).eval (Verification.environment w) = _
  rw [getElem!_pos (source10 (p := p)).toArray lane.val
    (by rw [Vector.size_toArray]; exact lane.isLt)]
  simpa using congrArg (fun row : Vector (ZMod p) 6 => row[lane]) (source10_eval w)

theorem query11_column {p : Nat} [Fact p.Prime]
    (w : Nat → ZMod p) (lane : Fin 6) :
    NativeLayout.queryColumn .diagonal 1 11 lane w = (source11Values w)[lane] := by
  unfold NativeLayout.queryColumn
  rw [source11_lookup]
  change ((source11 (p := p)).toArray[lane.val]!).eval (Verification.environment w) = _
  rw [getElem!_pos (source11 (p := p)).toArray lane.val
    (by rw [Vector.size_toArray]; exact lane.isLt)]
  simpa using congrArg (fun row : Vector (ZMod p) 6 => row[lane]) (source11_eval w)

theorem query14_column {p : Nat} [Fact p.Prime]
    (w : Nat → ZMod p) (lane : Fin 6) :
    NativeLayout.queryColumn .diagonal 1 14 lane w = (source14Values w)[lane] := by
  unfold NativeLayout.queryColumn
  rw [source14_lookup]
  change ((source14 (p := p)).toArray[lane.val]!).eval (Verification.environment w) = _
  rw [getElem!_pos (source14 (p := p)).toArray lane.val
    (by rw [Vector.size_toArray]; exact lane.isLt)]
  simpa using congrArg (fun row : Vector (ZMod p) 6 => row[lane]) (source14_eval w)

theorem query15_column {p : Nat} [Fact p.Prime]
    (w : Nat → ZMod p) (lane : Fin 6) :
    NativeLayout.queryColumn .diagonal 1 15 lane w = (source15Values w)[lane] := by
  unfold NativeLayout.queryColumn
  rw [source15_lookup]
  change ((source15 (p := p)).toArray[lane.val]!).eval (Verification.environment w) = _
  rw [getElem!_pos (source15 (p := p)).toArray lane.val
    (by rw [Vector.size_toArray]; exact lane.isLt)]
  simpa using congrArg (fun row : Vector (ZMod p) 6 => row[lane]) (source15_eval w)

def frame {p : Nat} (w : Nat → ZMod p) : Blake2G.Proofs.Frame p where
  inputs := #v[w 159 + w 175 + w 228 - 65536 * w 297 + w 318 + 128 * w 317 + w 230 - 65536 * w 321, w 161 + w 177 + w 229 + w 297 - 65536 * w 299 + w 319 + 128 * w 316 + w 231 + w 321 - 65536 * w 323, w 372 + 512 * w 375, w 373 + 512 * w 374, w 192 + w 384 + 256 * w 385 - 65536 * w 388 + w 404 + 256 * w 407 - 65536 * w 409, w 193 + w 382 + 256 * w 383 + w 388 - 65536 * w 391 + w 405 + 256 * w 406 + w 409 - 65536 * w 411, w 284 + 256 * w 287, w 285 + 256 * w 286, w 244, w 245, w 246, w 247]
  addCarries := #v[w 447, w 449, 30720 * w 43 - 30720 * w 159 - 30720 * w 175 - 30720 * w 228 - 30720 * w 230 - 30720 * w 244 - 30720 * w 246 - w 297 - 3932160 * w 317 - 30720 * w 318 - w 321 - 30720 * w 372 - 15728640 * w 375 - w 447 - 3932160 * w 465 - 30720 * w 466, -943718400 * w 43 + 30720 * w 44 + 943718400 * w 159 - 30720 * w 161 + 943718400 * w 175 - 30720 * w 177 + 943718400 * w 228 - 30720 * w 229 + 943718400 * w 230 - 30720 * w 231 + 943718400 * w 244 - 30720 * w 245 + 943718400 * w 246 - 30720 * w 247 - w 299 - 3932160 * w 316 - 60 * w 317 + 943718400 * w 318 - 30720 * w 319 - w 323 + 943718400 * w 372 - 30720 * w 373 - 15728640 * w 374 - 240 * w 375 - w 449 - 3932160 * w 464 - 60 * w 465 + 943718400 * w 466 - 30720 * w 467]
  cCarries := #v[w 456, w 459, 30720 * w 83 - 30720 * w 87 - 30720 * w 192 - 30720 * w 384 - 7864320 * w 385 - w 388 - 30720 * w 404 - 7864320 * w 407 - w 409 - 30720 * w 452 - 7864320 * w 453 - w 456, -943718400 * w 83 + 30720 * w 84 + 943718400 * w 87 - 30720 * w 88 + 943718400 * w 192 - 30720 * w 193 - 30720 * w 382 - 7864320 * w 383 + 943718400 * w 384 - 120 * w 385 - w 391 + 943718400 * w 404 - 30720 * w 405 - 7864320 * w 406 - 120 * w 407 - w 411 - 30720 * w 450 - 7864320 * w 451 + 943718400 * w 452 - 120 * w 453 - w 459]
  firstABytes := #v[w 446, w 448]
  dBytes := #v[w 284, w 285]
  firstDBytes := #v[w 450, w 451, w 452, w 453]
  bLow := #v[w 460, w 462]
  bMiddle := #v[w 461, w 463]
  cLow := #v[w 454, w 457]
  cMiddle := #v[w 455, w 458]
  firstBMiddle := #v[w 464, w 465]
  packedB := #v[w 466, w 467]
  secondABytes := #v[w 468, w 469]
  secondDBytes := #v[-7864320 * w 88 + 7864320 * w 471, w 470, -7864320 * w 87 + 7864320 * w 470, w 471]
  secondCLow := #v[w 472, w 473]
  secondBChunks := #v[-3932160 * w 64 + 3932160 * w 475, w 474, -3932160 * w 63 + 3932160 * w 474, w 475]

theorem frame_eq {p : Nat} [Fact p.Prime] (w : Nat → ZMod p) :
    diagonalFrame 1 w = frame w := by
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

end Airbender.Blake2Round.Proofs.NativeDiagonalView1
