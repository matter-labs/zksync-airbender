import Airbender.Proofs.Blake2Round.Mixing
import Airbender.Proofs.Blake2Round.DiagonalCertificate0
import Airbender.Proofs.Blake2Round.DiagonalCertificate1
import Airbender.Proofs.Blake2Round.DiagonalCertificate2
import Airbender.Proofs.Blake2Round.DiagonalCertificate3

namespace Airbender.Blake2Round.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

set_option maxHeartbeats 20000000 in
/-- The actual diagonal queries and carries imply the same native G fragment.
    Serialized coefficient compatibility is checked, rather than assuming a
    compiler correspondence or the desired mixing result. -/
theorem diagonal_g_holds {p : Nat} [Fact p.Prime]
    (compatible : 64 * (-31457280 : ZMod p) = 1) (call : Fin 4) {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints setupTable)) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment (diagonalGAssignment call w))
      (Blake2G.Proofs.mixingConstraints (Blake2G.setupTable (fun _ => Vector.replicate 7 0))) := by
  fin_cases call
  · exact diagonal_g_holds_0 compatible h
  · exact diagonal_g_holds_1 compatible h
  · exact diagonal_g_holds_2 compatible h
  · exact diagonal_g_holds_3 compatible h

private theorem diagonal_input_wiring {p : Nat} [Fact p.Prime]
    (call : Fin 4) (w : Nat → ZMod p) :
    nativeDiagonalAssignment call w 15 = nativeColumnAssignment call w 17 ∧
    nativeDiagonalAssignment call w 16 = nativeColumnAssignment call w 18 ∧
    nativeDiagonalAssignment call w 23 =
      nativeColumnAssignment (Fin.ofNat 4 (call.val + 2)) w 25 ∧
    nativeDiagonalAssignment call w 24 =
      nativeColumnAssignment (Fin.ofNat 4 (call.val + 2)) w 26 := by
  simp [nativeDiagonalAssignment, Blake2G.Proofs.Frame.assignment,
    Blake2G.Proofs.assemble, Blake2G.Proofs.Frame.base, diagonalFrame,
    NativeLayout.Layout.read, NativeLayout.diagonal,  NativeLayout.Location.read,
    diagonalIncoming]

/-- The two diagonal addition-input bounds come from column queries, not
    another interface assumption. Only the two selected message bounds remain. -/
theorem diagonal_g_input_bounds {p : Nat} [Fact p.Prime] (hp : 65536 ≤ p)
    (compatible : 64 * (-31457280 : ZMod p) = 1) (call : Fin 4)
    {w : Nat → ZMod p} {input : Blake2G.Input} {output : Blake2G.Words}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints setupTable))
    (mapping : Blake2G.WordMapping input output (diagonalGAssignment call w)) :
    input.state.a.Bounded ∧ input.state.c.Bounded := by
  have a := Blake2G.Proofs.mixing_output_bounds hp compatible (column_g_holds (by omega) call h)
  have c := Blake2G.Proofs.mixing_output_bounds hp compatible
    (column_g_holds (by omega) (Fin.ofNat 4 (call.val + 2)) h)
  have wires := diagonal_input_wiring call w
  simp only [mapping.stateReads, diagonalGAssignment, wires.1, wires.2.1,
    wires.2.2.1, wires.2.2.2]
  exact ⟨a.1, c.2.2.1⟩

theorem diagonal_g_soundness {p : Nat} [Fact p.Prime] (hp : 262144 ≤ p)
    (compatible : 64 * (-31457280 : ZMod p) = 1) (call : Fin 4)
    {w : Nat → ZMod p} {input : Blake2G.Input} {output : Blake2G.Words}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints setupTable))
    (mapping : Blake2G.WordMapping input output (diagonalGAssignment call w))
    (messageXBound : input.mx.Bounded) (messageYBound : input.my.Bounded) :
    Blake2G.spec input output := by
  have bounds := diagonal_g_input_bounds (by omega) compatible call h mapping
  exact Blake2G.Proofs.mixing_soundness hp compatible (fun _ => Vector.replicate 7 0)
    input output (diagonalGAssignment call w)
      ⟨⟨bounds.1, bounds.2, messageXBound, messageYBound⟩,
        diagonal_g_holds compatible call h, mapping⟩

theorem diagonal_g_output_bounds {p : Nat} [Fact p.Prime] (hp : 65536 ≤ p)
    (compatible : 64 * (-31457280 : ZMod p) = 1) (call : Fin 4)
    {w : Nat → ZMod p} {input : Blake2G.Input} {output : Blake2G.Words}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints setupTable))
    (mapping : Blake2G.WordMapping input output (diagonalGAssignment call w)) :
    output.a.Bounded ∧ output.b.Bounded ∧ output.c.Bounded ∧ output.d.Bounded := by
  have bounds := Blake2G.Proofs.mixing_output_bounds hp compatible
    (diagonal_g_holds compatible call h)
  rw [mapping.stateWrites]
  exact bounds

end Airbender.Blake2Round.Proofs
