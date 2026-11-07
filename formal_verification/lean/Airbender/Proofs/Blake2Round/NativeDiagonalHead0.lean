import Airbender.Proofs.Blake2Round.NativeDiagonalView0
import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Review.Helpers.Core.SerializedInverse
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
  exact NativeDiagonalView0.source0_eval w


theorem source1_eval {p : Nat} [Fact p.Prime] (w : Nat → ZMod p) :
    source1.map (Expression.eval (Verification.environment w)) =
      #v[w 407, highA w, w 421, 0, 0, 4] := by
  exact NativeDiagonalView0.source1_eval w


theorem source2_eval {p : Nat} [Fact p.Prime] (w : Nat → ZMod p) :
    source2.map (Expression.eval (Verification.environment w)) =
      #v[w 405, w 418, w 419, w 422, 0, 55] := by
  exact NativeDiagonalView0.source2_eval w


theorem d_byte0 {p : Nat} [Fact p.Prime] (w : Nat → ZMod p) :
    (diagonalFrame 0 w).dBytes[0] = w 404 := by
  rw [NativeDiagonalView0.frame_eq]
  rfl


theorem d_byte1 {p : Nat} [Fact p.Prime] (w : Nat → ZMod p) :
    (diagonalFrame 0 w).dBytes[1] = w 405 := by
  rw [NativeDiagonalView0.frame_eq]
  rfl


theorem d_input {p : Nat} [Fact p.Prime] (w : Nat → ZMod p) :
    (diagonalFrame 0 w).inputs[6] = w 404 + 256 * w 407 := by
  rw [NativeDiagonalView0.frame_eq]
  rfl


theorem a_input_sum {p : Nat} [Fact p.Prime] (w : Nat → ZMod p) :
    let f := diagonalFrame 0 w
    f.inputs[0] + f.inputs[2] + f.inputs[8] -
      65536 * f.addCarries[0] - f.firstABytes[0] =
    w 155 + w 171 + w 224 + w 226 + w 240 -
      65536 * w 257 - 65536 * w 281 + w 278 + 128 * w 277 +
      w 332 + 512 * w 335 - 65536 * w 417 - w 416 := by
  rw [NativeDiagonalView0.frame_eq]
  simp only [NativeDiagonalView0.frame, Vector.getElem_mk,
    List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
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
  rw [NativeDiagonalView0.frame_eq]
  simp [carryPad, NativeDiagonalView0.frame]

theorem columns1 {p : Nat} [Fact p.Prime]
    (compatible : SerializedInverse.Scale64 p)
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
  rw [NativeDiagonalView0.frame_eq]
  apply Vector.ext
  intro lane bound
  change lane < 9 at bound
  interval_cases lane
  all_goals simp [highA, plainPad, NativeDiagonalView0.frame]
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
  rw [NativeDiagonalView0.frame_eq]
  simp [carryPad, NativeDiagonalView0.frame]

/-- Transfer the first three native diagonal queries through checked row interfaces. -/
theorem native_diagonal_head0_queries {p : Nat} [Fact p.Prime] (hp : FieldCapacity.AtLeast p 512)
    (compatible : SerializedInverse.Scale64 p)
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
