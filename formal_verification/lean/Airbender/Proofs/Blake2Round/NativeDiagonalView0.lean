import Airbender.Proofs.Blake2Round.NativeDiagonalSources0
import Airbender.Proofs.Blake2Round.NativeDiagonalAssignment
import Airbender.Proofs.Blake2G.FrameNormalization

namespace Airbender.Blake2Round.Proofs.NativeDiagonalView0
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

theorem query0_column {p : Nat} [Fact p.Prime]
    (w : Nat → ZMod p) (lane : Fin 6) :
    NativeLayout.queryColumn .diagonal 0 0 lane w = (source0Values w)[lane] := by
  unfold NativeLayout.queryColumn
  rw [source0_lookup]
  change ((source0 (p := p)).toArray[lane.val]!).eval (Verification.environment w) = _
  rw [getElem!_pos (source0 (p := p)).toArray lane.val
    (by rw [Vector.size_toArray]; exact lane.isLt)]
  simpa using congrArg (fun row : Vector (ZMod p) 6 => row[lane]) (source0_eval w)

theorem query2_column {p : Nat} [Fact p.Prime]
    (w : Nat → ZMod p) (lane : Fin 6) :
    NativeLayout.queryColumn .diagonal 0 2 lane w = (source2Values w)[lane] := by
  unfold NativeLayout.queryColumn
  rw [source2_lookup]
  change ((source2 (p := p)).toArray[lane.val]!).eval (Verification.environment w) = _
  rw [getElem!_pos (source2 (p := p)).toArray lane.val
    (by rw [Vector.size_toArray]; exact lane.isLt)]
  simpa using congrArg (fun row : Vector (ZMod p) 6 => row[lane]) (source2_eval w)

theorem query10_column {p : Nat} [Fact p.Prime]
    (w : Nat → ZMod p) (lane : Fin 6) :
    NativeLayout.queryColumn .diagonal 0 10 lane w = (source10Values w)[lane] := by
  unfold NativeLayout.queryColumn
  rw [source10_lookup]
  change ((source10 (p := p)).toArray[lane.val]!).eval (Verification.environment w) = _
  rw [getElem!_pos (source10 (p := p)).toArray lane.val
    (by rw [Vector.size_toArray]; exact lane.isLt)]
  simpa using congrArg (fun row : Vector (ZMod p) 6 => row[lane]) (source10_eval w)

theorem query11_column {p : Nat} [Fact p.Prime]
    (w : Nat → ZMod p) (lane : Fin 6) :
    NativeLayout.queryColumn .diagonal 0 11 lane w = (source11Values w)[lane] := by
  unfold NativeLayout.queryColumn
  rw [source11_lookup]
  change ((source11 (p := p)).toArray[lane.val]!).eval (Verification.environment w) = _
  rw [getElem!_pos (source11 (p := p)).toArray lane.val
    (by rw [Vector.size_toArray]; exact lane.isLt)]
  simpa using congrArg (fun row : Vector (ZMod p) 6 => row[lane]) (source11_eval w)

theorem query14_column {p : Nat} [Fact p.Prime]
    (w : Nat → ZMod p) (lane : Fin 6) :
    NativeLayout.queryColumn .diagonal 0 14 lane w = (source14Values w)[lane] := by
  unfold NativeLayout.queryColumn
  rw [source14_lookup]
  change ((source14 (p := p)).toArray[lane.val]!).eval (Verification.environment w) = _
  rw [getElem!_pos (source14 (p := p)).toArray lane.val
    (by rw [Vector.size_toArray]; exact lane.isLt)]
  simpa using congrArg (fun row : Vector (ZMod p) 6 => row[lane]) (source14_eval w)

theorem query15_column {p : Nat} [Fact p.Prime]
    (w : Nat → ZMod p) (lane : Fin 6) :
    NativeLayout.queryColumn .diagonal 0 15 lane w = (source15Values w)[lane] := by
  unfold NativeLayout.queryColumn
  rw [source15_lookup]
  change ((source15 (p := p)).toArray[lane.val]!).eval (Verification.environment w) = _
  rw [getElem!_pos (source15 (p := p)).toArray lane.val
    (by rw [Vector.size_toArray]; exact lane.isLt)]
  simpa using congrArg (fun row : Vector (ZMod p) 6 => row[lane]) (source15_eval w)

def frame {p : Nat} (w : Nat → ZMod p) : Blake2G.Proofs.Frame p where
  inputs := #v[w 155 + w 171 + w 224 - 65536 * w 257 + w 278 + 128 * w 277 + w 226 - 65536 * w 281, w 157 + w 173 + w 225 + w 257 - 65536 * w 259 + w 279 + 128 * w 276 + w 227 + w 281 - 65536 * w 283, w 332 + 512 * w 335, w 333 + 512 * w 334, w 190 + w 344 + 256 * w 345 - 65536 * w 348 + w 364 + 256 * w 367 - 65536 * w 369, w 191 + w 342 + 256 * w 343 + w 348 - 65536 * w 351 + w 365 + 256 * w 366 + w 369 - 65536 * w 371, w 404 + 256 * w 407, w 405 + 256 * w 406, w 240, w 241, w 242, w 243]
  addCarries := #v[w 417, w 419, 30720 * w 39 - 30720 * w 155 - 30720 * w 171 - 30720 * w 224 - 30720 * w 226 - 30720 * w 240 - 30720 * w 242 - w 257 - 3932160 * w 277 - 30720 * w 278 - w 281 - 30720 * w 332 - 15728640 * w 335 - w 417 - 3932160 * w 435 - 30720 * w 436, -943718400 * w 39 + 30720 * w 40 + 943718400 * w 155 - 30720 * w 157 + 943718400 * w 171 - 30720 * w 173 + 943718400 * w 224 - 30720 * w 225 + 943718400 * w 226 - 30720 * w 227 + 943718400 * w 240 - 30720 * w 241 + 943718400 * w 242 - 30720 * w 243 - w 259 - 3932160 * w 276 - 60 * w 277 + 943718400 * w 278 - 30720 * w 279 - w 283 + 943718400 * w 332 - 30720 * w 333 - 15728640 * w 334 - 240 * w 335 - w 419 - 3932160 * w 434 - 60 * w 435 + 943718400 * w 436 - 30720 * w 437]
  cCarries := #v[w 426, w 429, 30720 * w 79 - 30720 * w 99 - 30720 * w 190 - 30720 * w 344 - 7864320 * w 345 - w 348 - 30720 * w 364 - 7864320 * w 367 - w 369 - 30720 * w 422 - 7864320 * w 423 - w 426, -943718400 * w 79 + 30720 * w 80 + 943718400 * w 99 - 30720 * w 100 + 943718400 * w 190 - 30720 * w 191 - 30720 * w 342 - 7864320 * w 343 + 943718400 * w 344 - 120 * w 345 - w 351 + 943718400 * w 364 - 30720 * w 365 - 7864320 * w 366 - 120 * w 367 - w 371 - 30720 * w 420 - 7864320 * w 421 + 943718400 * w 422 - 120 * w 423 - w 429]
  firstABytes := #v[w 416, w 418]
  dBytes := #v[w 404, w 405]
  firstDBytes := #v[w 420, w 421, w 422, w 423]
  bLow := #v[w 430, w 432]
  bMiddle := #v[w 431, w 433]
  cLow := #v[w 424, w 427]
  cMiddle := #v[w 425, w 428]
  firstBMiddle := #v[w 434, w 435]
  packedB := #v[w 436, w 437]
  secondABytes := #v[w 438, w 439]
  secondDBytes := #v[-7864320 * w 100 + 7864320 * w 441, w 440, -7864320 * w 99 + 7864320 * w 440, w 441]
  secondCLow := #v[w 442, w 443]
  secondBChunks := #v[-3932160 * w 60 + 3932160 * w 445, w 444, -3932160 * w 59 + 3932160 * w 444, w 445]

theorem frame_eq {p : Nat} [Fact p.Prime] (w : Nat → ZMod p) :
    diagonalFrame 0 w = frame w := by
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

end Airbender.Blake2Round.Proofs.NativeDiagonalView0
