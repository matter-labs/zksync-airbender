import Airbender.Proofs.Blake2Round.NativeDiagonalSources3
import Airbender.Proofs.Blake2Round.NativeDiagonalAssignment
import Airbender.Proofs.Blake2G.FrameNormalization

namespace Airbender.Blake2Round.Proofs.NativeDiagonalView3
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

theorem query0_column {p : Nat} [Fact p.Prime]
    (w : Nat → ZMod p) (lane : Fin 6) :
    NativeLayout.queryColumn .diagonal 3 0 lane w = (source0Values w)[lane] := by
  unfold NativeLayout.queryColumn
  rw [source0_lookup]
  change ((source0 (p := p)).toArray[lane.val]!).eval (Verification.environment w) = _
  rw [getElem!_pos (source0 (p := p)).toArray lane.val
    (by rw [Vector.size_toArray]; exact lane.isLt)]
  simpa using congrArg (fun row : Vector (ZMod p) 6 => row[lane]) (source0_eval w)

theorem query2_column {p : Nat} [Fact p.Prime]
    (w : Nat → ZMod p) (lane : Fin 6) :
    NativeLayout.queryColumn .diagonal 3 2 lane w = (source2Values w)[lane] := by
  unfold NativeLayout.queryColumn
  rw [source2_lookup]
  change ((source2 (p := p)).toArray[lane.val]!).eval (Verification.environment w) = _
  rw [getElem!_pos (source2 (p := p)).toArray lane.val
    (by rw [Vector.size_toArray]; exact lane.isLt)]
  simpa using congrArg (fun row : Vector (ZMod p) 6 => row[lane]) (source2_eval w)

theorem query10_column {p : Nat} [Fact p.Prime]
    (w : Nat → ZMod p) (lane : Fin 6) :
    NativeLayout.queryColumn .diagonal 3 10 lane w = (source10Values w)[lane] := by
  unfold NativeLayout.queryColumn
  rw [source10_lookup]
  change ((source10 (p := p)).toArray[lane.val]!).eval (Verification.environment w) = _
  rw [getElem!_pos (source10 (p := p)).toArray lane.val
    (by rw [Vector.size_toArray]; exact lane.isLt)]
  simpa using congrArg (fun row : Vector (ZMod p) 6 => row[lane]) (source10_eval w)

theorem query11_column {p : Nat} [Fact p.Prime]
    (w : Nat → ZMod p) (lane : Fin 6) :
    NativeLayout.queryColumn .diagonal 3 11 lane w = (source11Values w)[lane] := by
  unfold NativeLayout.queryColumn
  rw [source11_lookup]
  change ((source11 (p := p)).toArray[lane.val]!).eval (Verification.environment w) = _
  rw [getElem!_pos (source11 (p := p)).toArray lane.val
    (by rw [Vector.size_toArray]; exact lane.isLt)]
  simpa using congrArg (fun row : Vector (ZMod p) 6 => row[lane]) (source11_eval w)

theorem query14_column {p : Nat} [Fact p.Prime]
    (w : Nat → ZMod p) (lane : Fin 6) :
    NativeLayout.queryColumn .diagonal 3 14 lane w = (source14Values w)[lane] := by
  unfold NativeLayout.queryColumn
  rw [source14_lookup]
  change ((source14 (p := p)).toArray[lane.val]!).eval (Verification.environment w) = _
  rw [getElem!_pos (source14 (p := p)).toArray lane.val
    (by rw [Vector.size_toArray]; exact lane.isLt)]
  simpa using congrArg (fun row : Vector (ZMod p) 6 => row[lane]) (source14_eval w)

theorem query15_column {p : Nat} [Fact p.Prime]
    (w : Nat → ZMod p) (lane : Fin 6) :
    NativeLayout.queryColumn .diagonal 3 15 lane w = (source15Values w)[lane] := by
  unfold NativeLayout.queryColumn
  rw [source15_lookup]
  change ((source15 (p := p)).toArray[lane.val]!).eval (Verification.environment w) = _
  rw [getElem!_pos (source15 (p := p)).toArray lane.val
    (by rw [Vector.size_toArray]; exact lane.isLt)]
  simpa using congrArg (fun row : Vector (ZMod p) 6 => row[lane]) (source15_eval w)

def frame {p : Nat} (w : Nat → ZMod p) : Blake2G.Proofs.Frame p where
  inputs := #v[w 167 + w 183 + w 236 - 65536 * w 377 + w 398 + 128 * w 397 + w 238 - 65536 * w 401, w 169 + w 185 + w 237 + w 377 - 65536 * w 379 + w 399 + 128 * w 396 + w 239 + w 401 - 65536 * w 403, w 292 + 512 * w 295, w 293 + 512 * w 294, w 188 + w 304 + 256 * w 305 - 65536 * w 308 + w 324 + 256 * w 327 - 65536 * w 329, w 189 + w 302 + 256 * w 303 + w 308 - 65536 * w 311 + w 325 + 256 * w 326 + w 329 - 65536 * w 331, w 364 + 256 * w 367, w 365 + 256 * w 366, w 252, w 253, w 254, w 255]
  addCarries := #v[w 507, w 509, 30720 * w 51 - 30720 * w 167 - 30720 * w 183 - 30720 * w 236 - 30720 * w 238 - 30720 * w 252 - 30720 * w 254 - 30720 * w 292 - 15728640 * w 295 - w 377 - 3932160 * w 397 - 30720 * w 398 - w 401 - w 507 - 3932160 * w 525 - 30720 * w 526, -943718400 * w 51 + 30720 * w 52 + 943718400 * w 167 - 30720 * w 169 + 943718400 * w 183 - 30720 * w 185 + 943718400 * w 236 - 30720 * w 237 + 943718400 * w 238 - 30720 * w 239 + 943718400 * w 252 - 30720 * w 253 + 943718400 * w 254 - 30720 * w 255 + 943718400 * w 292 - 30720 * w 293 - 15728640 * w 294 - 240 * w 295 - w 379 - 3932160 * w 396 - 60 * w 397 + 943718400 * w 398 - 30720 * w 399 - w 403 - w 509 - 3932160 * w 524 - 60 * w 525 + 943718400 * w 526 - 30720 * w 527]
  cCarries := #v[w 516, w 519, 30720 * w 75 - 30720 * w 95 - 30720 * w 188 - 30720 * w 304 - 7864320 * w 305 - w 308 - 30720 * w 324 - 7864320 * w 327 - w 329 - 30720 * w 512 - 7864320 * w 513 - w 516, -943718400 * w 75 + 30720 * w 76 + 943718400 * w 95 - 30720 * w 96 + 943718400 * w 188 - 30720 * w 189 - 30720 * w 302 - 7864320 * w 303 + 943718400 * w 304 - 120 * w 305 - w 311 + 943718400 * w 324 - 30720 * w 325 - 7864320 * w 326 - 120 * w 327 - w 331 - 30720 * w 510 - 7864320 * w 511 + 943718400 * w 512 - 120 * w 513 - w 519]
  firstABytes := #v[w 506, w 508]
  dBytes := #v[w 364, w 365]
  firstDBytes := #v[w 510, w 511, w 512, w 513]
  bLow := #v[w 520, w 522]
  bMiddle := #v[w 521, w 523]
  cLow := #v[w 514, w 517]
  cMiddle := #v[w 515, w 518]
  firstBMiddle := #v[w 524, w 525]
  packedB := #v[w 526, w 527]
  secondABytes := #v[w 528, w 529]
  secondDBytes := #v[-7864320 * w 96 + 7864320 * w 531, w 530, -7864320 * w 95 + 7864320 * w 530, w 531]
  secondCLow := #v[w 532, w 533]
  secondBChunks := #v[-3932160 * w 56 + 3932160 * w 535, w 534, -3932160 * w 55 + 3932160 * w 534, w 535]

theorem frame_eq {p : Nat} [Fact p.Prime] (w : Nat → ZMod p) :
    diagonalFrame 3 w = frame w := by
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

end Airbender.Blake2Round.Proofs.NativeDiagonalView3
