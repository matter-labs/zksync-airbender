import Airbender.Proofs.Blake2G.FrameQueryShapes
import Airbender.Proofs.Blake2Round.NativeDiagonalAssignment
import Airbender.Proofs.Blake2Round.NativeXorTransfer
import Airbender.Proofs.Blake2Round.ArtifactChecks
import Airbender.Proofs.Constraints

namespace Airbender.Blake2Round.Proofs.NativeDiagonalHead0
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

open Blake2G.Proofs.FrameQueryShapes

def source0 {p : Nat} [Fact p.Prime] : Vector (Expression (ZMod p)) 6 :=
  ((FlatOperation.lookups (importedConstraints setupTable)).get
    ⟨66, by rw [lookup_count]; decide⟩).entry

def source1 {p : Nat} [Fact p.Prime] : Vector (Expression (ZMod p)) 6 :=
  ((FlatOperation.lookups (importedConstraints setupTable)).get
    ⟨67, by rw [lookup_count]; decide⟩).entry

def source2 {p : Nat} [Fact p.Prime] : Vector (Expression (ZMod p)) 6 :=
  ((FlatOperation.lookups (importedConstraints setupTable)).get
    ⟨68, by rw [lookup_count]; decide⟩).entry

theorem source0_lookup {p : Nat} [Fact p.Prime] :
    ((FlatOperation.lookups (importedConstraints setupTable)).get
      ⟨NativeLayout.queryIndex .diagonal (0 : Fin 4)
        NativeLayout.legacyQuerySources[(0 : Fin 18)],
        by rw [lookup_count]; norm_num [NativeLayout.queryIndex, NativeLayout.legacyQuerySources]⟩) =
      Lookup.mk setupTable.toRaw (source0 (p := p)) := rfl

theorem source1_lookup {p : Nat} [Fact p.Prime] :
    ((FlatOperation.lookups (importedConstraints setupTable)).get
      ⟨NativeLayout.queryIndex .diagonal (0 : Fin 4)
        NativeLayout.legacyQuerySources[(1 : Fin 18)],
        by rw [lookup_count]; norm_num [NativeLayout.queryIndex, NativeLayout.legacyQuerySources]⟩) =
      Lookup.mk setupTable.toRaw (source1 (p := p)) := rfl

theorem source2_lookup {p : Nat} [Fact p.Prime] :
    ((FlatOperation.lookups (importedConstraints setupTable)).get
      ⟨NativeLayout.queryIndex .diagonal (0 : Fin 4)
        NativeLayout.legacyQuerySources[(2 : Fin 18)],
        by rw [lookup_count]; norm_num [NativeLayout.queryIndex, NativeLayout.legacyQuerySources]⟩) =
      Lookup.mk setupTable.toRaw (source2 (p := p)) := rfl

def highA {p : Nat} (w : Nat → ZMod p) : ZMod p :=
  -7864320 * w 155 - 7864320 * w 171 - 7864320 * w 224 -
  7864320 * w 226 - 7864320 * w 240 - 256 * w 257 -
  1006632960 * w 277 - 7864320 * w 278 - 256 * w 281 -
  7864320 * w 332 + 2 * w 335 + 7864320 * w 416 - 256 * w 417

theorem source0_eval {p : Nat} [Fact p.Prime] (w : Nat → ZMod p) :
    source0.map (Expression.eval (Verification.environment w)) =
      #v[w 404, w 416, w 417, w 420, 0, 55] := by
  apply Vector.ext
  intro lane bound
  change lane < 6 at bound
  interval_cases lane
  all_goals simp [source0, importedConstraints, FlatOperation.lookups,
    Expression.eval, Verification.environment]

theorem source1_eval {p : Nat} [Fact p.Prime] (w : Nat → ZMod p) :
    source1.map (Expression.eval (Verification.environment w)) =
      #v[w 407, highA w, w 421, 0, 0, 4] := by
  apply Vector.ext
  intro lane bound
  change lane < 6 at bound
  interval_cases lane
  all_goals simp [source1, importedConstraints, FlatOperation.lookups,
    Expression.eval, Verification.environment, highA]
  all_goals ring

theorem source2_eval {p : Nat} [Fact p.Prime] (w : Nat → ZMod p) :
    source2.map (Expression.eval (Verification.environment w)) =
      #v[w 405, w 418, w 419, w 422, 0, 55] := by
  apply Vector.ext
  intro lane bound
  change lane < 6 at bound
  interval_cases lane
  all_goals simp [source2, importedConstraints, FlatOperation.lookups,
    Expression.eval, Verification.environment]

theorem d_byte0 {p : Nat} [Fact p.Prime] (w : Nat → ZMod p) :
    (diagonalFrame 0 w).dBytes[0] = w 404 := by
  have column := congrArg (fun row : Vector (ZMod p) 6 => row[0]) (source0_eval w)
  have projection : (diagonalFrame 0 w).dBytes[0] =
      ((source0 (p := p)).toArray[0]!).eval (Verification.environment w) := by
    simp [source0, diagonalFrame, NativeLayout.diagonal, NativeLayout.Layout.read,
      NativeLayout.Location.read, NativeLayout.queryColumn, NativeLayout.queryIndex]
    rw [getElem!_pos _ 0 (by change 0 < 6; decide)]
    rfl
  rw [projection, getElem!_pos (source0 (p := p)).toArray 0
    (by rw [Vector.size_toArray]; decide)]
  simpa using column

theorem d_byte1 {p : Nat} [Fact p.Prime] (w : Nat → ZMod p) :
    (diagonalFrame 0 w).dBytes[1] = w 405 := by
  have column := congrArg (fun row : Vector (ZMod p) 6 => row[0]) (source2_eval w)
  have projection : (diagonalFrame 0 w).dBytes[1] =
      ((source2 (p := p)).toArray[0]!).eval (Verification.environment w) := by
    simp [source2, diagonalFrame, NativeLayout.diagonal, NativeLayout.Layout.read,
      NativeLayout.Location.read, NativeLayout.queryColumn, NativeLayout.queryIndex]
    rw [getElem!_pos _ 0 (by change 0 < 6; decide)]
    rfl
  rw [projection, getElem!_pos (source2 (p := p)).toArray 0
    (by rw [Vector.size_toArray]; decide)]
  simpa using column

theorem d_input {p : Nat} [Fact p.Prime] (w : Nat → ZMod p) :
    (diagonalFrame 0 w).inputs[6] = w 404 + 256 * w 407 := by
  simp [diagonalFrame, diagonalIncoming, NativeLayout.diagonal, NativeLayout.Layout.read,
    NativeLayout.Location.read, nativeColumnAssignment,
    Blake2G.Proofs.Frame.assignment_eq_normalized, Blake2G.Proofs.Frame.normalizedAssignment,
    columnFrame, NativeLayout.column, NativeLayout.columnInputs]

theorem a_input_sum {p : Nat} [Fact p.Prime] (w : Nat → ZMod p) :
    let f := diagonalFrame 0 w
    f.inputs[0] + f.inputs[2] + f.inputs[8] -
      65536 * f.addCarries[0] - f.firstABytes[0] =
    w 155 + w 171 + w 224 + w 226 + w 240 -
      65536 * w 257 - 65536 * w 281 + w 278 + 128 * w 277 +
      w 332 + 512 * w 335 - 65536 * w 417 - w 416 := by
  simp [diagonalFrame, diagonalIncoming, NativeLayout.diagonal, NativeLayout.Layout.read,
    NativeLayout.Location.read, nativeColumnAssignment,
    Blake2G.Proofs.Frame.assignment_eq_normalized, Blake2G.Proofs.Frame.normalizedAssignment,
    columnFrame, NativeLayout.column, NativeLayout.columnInputs]
  ring

theorem columns0 {p : Nat} [Fact p.Prime]
    (control : Fin 512 → Vector Nat 7) (w : Nat → ZMod p) :
    (entry0 (Blake2G.setupTable control)).map
        (Expression.eval (Verification.environment (nativeDiagonalAssignment 0 w))) =
      carryPad 0 (source0.map (Expression.eval (Verification.environment w))) := by
  change (entry0 (Blake2G.setupTable control)).map
    (Expression.eval (Verification.environment (diagonalFrame 0 w).assignment)) = _
  rw [row0, source0_eval]
  rw [d_byte0]
  simp [carryPad, diagonalFrame, NativeLayout.diagonal, NativeLayout.Layout.read,
    NativeLayout.Location.read]

theorem columns1 {p : Nat} [Fact p.Prime]
    (compatible : 64 * (-31457280 : ZMod p) = 1)
    (control : Fin 512 → Vector Nat 7) (w : Nat → ZMod p) :
    (entry1 (Blake2G.setupTable control)).map
        (Expression.eval (Verification.environment (nativeDiagonalAssignment 0 w))) =
      plainPad (source1.map (Expression.eval (Verification.environment w))) := by
  change (entry1 (Blake2G.setupTable control)).map
    (Expression.eval (Verification.environment (diagonalFrame 0 w).assignment)) = _
  rw [row1 compatible, source1_eval, d_input, d_byte0, a_input_sum]
  have inverse := Blake2G.Proofs.inverse256 compatible
  have scale : (-7864320 : ZMod p) * 65536 = 256 := by
    linear_combination 256 * inverse
  apply Vector.ext
  intro lane bound
  change lane < 9 at bound
  interval_cases lane
  all_goals simp [highA, plainPad, diagonalFrame, NativeLayout.diagonal,
    NativeLayout.Layout.read, NativeLayout.Location.read]
  · linear_combination w 407 * inverse
  · linear_combination -(w 257 + w 281 + w 417) * scale + 2 * w 335 * inverse

theorem columns2 {p : Nat} [Fact p.Prime]
    (control : Fin 512 → Vector Nat 7) (w : Nat → ZMod p) :
    (entry2 (Blake2G.setupTable control)).map
        (Expression.eval (Verification.environment (nativeDiagonalAssignment 0 w))) =
      carryPad 0 (source2.map (Expression.eval (Verification.environment w))) := by
  change (entry2 (Blake2G.setupTable control)).map
    (Expression.eval (Verification.environment (diagonalFrame 0 w).assignment)) = _
  rw [row2, source2_eval]
  rw [d_byte1]
  simp [carryPad, diagonalFrame, NativeLayout.diagonal, NativeLayout.Layout.read,
    NativeLayout.Location.read]

/-- Transfer the first three native diagonal queries through checked row interfaces. -/
theorem native_diagonal_head0_queries {p : Nat} [Fact p.Prime] (hp : 512 ≤ p)
    (compatible : 64 * (-31457280 : ZMod p) = 1)
    {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints setupTable)) (i : Fin 3) :
    ((FlatOperation.lookups (Blake2G.Proofs.mixingConstraints
      (Blake2G.setupTable (fun _ => Vector.replicate 7 0)))).get
      ⟨0 + i.val, by rw [Blake2G.Proofs.mixing_lookup_count]; have := i.isLt; omega⟩).Contains
        (Verification.environment (nativeDiagonalAssignment 0 w)) := by
  fin_cases i
  · have member := Verification.lookup_of_holds h
      ⟨NativeLayout.queryIndex .diagonal (0 : Fin 4) NativeLayout.legacyQuerySources[(0 : Fin 18)],
        by rw [lookup_count]; norm_num [NativeLayout.queryIndex, NativeLayout.legacyQuerySources]⟩
    rw [source0_lookup] at member
    change ((FlatOperation.lookups (Blake2G.Proofs.mixingConstraints
      (Blake2G.setupTable (fun _ => Vector.replicate 7 0)))).get
      ⟨0, by rw [Blake2G.Proofs.mixing_lookup_count]; decide⟩).Contains
      (Verification.environment (nativeDiagonalAssignment 0 w))
    rw [lookup0_eq_mk]
    apply carry_membership hp (fun _ => Vector.replicate 7 0) 0 member
    · simpa [carryTags] using
        congrArg (fun row : Vector (ZMod p) 6 => row[5]) (source0_eval w)
    · exact columns0 _ w
  · have member := Verification.lookup_of_holds h
      ⟨NativeLayout.queryIndex .diagonal (0 : Fin 4) NativeLayout.legacyQuerySources[(1 : Fin 18)],
        by rw [lookup_count]; norm_num [NativeLayout.queryIndex, NativeLayout.legacyQuerySources]⟩
    rw [source1_lookup] at member
    change ((FlatOperation.lookups (Blake2G.Proofs.mixingConstraints
      (Blake2G.setupTable (fun _ => Vector.replicate 7 0)))).get
      ⟨1, by rw [Blake2G.Proofs.mixing_lookup_count]; decide⟩).Contains
      (Verification.environment (nativeDiagonalAssignment 0 w))
    rw [lookup1_eq_mk]
    apply plain_membership hp (fun _ => Vector.replicate 7 0) 0 member
    · simpa [plainTags] using
        congrArg (fun row : Vector (ZMod p) 6 => row[5]) (source1_eval w)
    · exact columns1 compatible _ w
  · have member := Verification.lookup_of_holds h
      ⟨NativeLayout.queryIndex .diagonal (0 : Fin 4) NativeLayout.legacyQuerySources[(2 : Fin 18)],
        by rw [lookup_count]; norm_num [NativeLayout.queryIndex, NativeLayout.legacyQuerySources]⟩
    rw [source2_lookup] at member
    change ((FlatOperation.lookups (Blake2G.Proofs.mixingConstraints
      (Blake2G.setupTable (fun _ => Vector.replicate 7 0)))).get
      ⟨2, by rw [Blake2G.Proofs.mixing_lookup_count]; decide⟩).Contains
      (Verification.environment (nativeDiagonalAssignment 0 w))
    rw [lookup2_eq_mk]
    apply carry_membership hp (fun _ => Vector.replicate 7 0) 0 member
    · simpa [carryTags] using
        congrArg (fun row : Vector (ZMod p) 6 => row[5]) (source2_eval w)
    · exact columns2 _ w

end Airbender.Blake2Round.Proofs.NativeDiagonalHead0
