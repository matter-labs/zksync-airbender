import Human.Circuits.Blake2Round.Finalization
import Slop.Constraints
import Slop.Blake2Round.FinalWriteback
import Mathlib.Tactic.LinearCombination

set_option warningAsError true

namespace Airbender.Blake2Round.Proofs

set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

theorem nonfinal_reference {p : Nat} {input : Finalization.Input} {output : Finalization.Output}
    {w : Nat → ZMod p} (interface : Finalization.NonFinalAssumptions input output w) :
    Finalization.isFinal input = false := by
  have last : input.round ≠ 9 := fun eq => interface.nonFinal.1 (congrArg Fin.val eq)
  cases reduced : input.reducedRounds
  · simp [Finalization.isFinal, reduced, last]
  · have seventh : input.round ≠ 6 := fun eq =>
      interface.nonFinal.2 reduced (congrArg Fin.val eq)
    simp [Finalization.isFinal, reduced, last, seventh]

/-- The actual selector equation agrees with the final-round rule for all
    twenty round/mode combinations under the exclusive caller mask. -/
theorem finalization_flag {p : Nat} [Fact p.Prime]
    {setup : Table (ZMod p) (fields 4)} {w : Nat → ZMod p}
    {input : Finalization.Input} {output : Finalization.Output}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (mapping : Finalization.WordMapping input output w)
    (roundMask : ∀ i : Fin 10, w Variables.roundBits[i] = if i = input.round then 1 else 0) :
    w 152 = if Finalization.isFinal input then 1 else 0 := by
  have flag := Verification.assertion_of_holds h ⟨2, by rw [constraint_count]; decide⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval,
    Verification.environment] at flag
  have equation : w 152 = w 148 * w 139 + w 151 := by linear_combination -flag
  have mask6 := roundMask 6
  have mask9 := roundMask 9
  have reduced := mapping.reduced
  simp [Variables.roundBits, Variables.controlBits] at mask6 mask9 reduced
  rw [equation, mask6, mask9, reduced]
  rcases input with ⟨round, mode, state, chaining, extended⟩
  cases mode <;> fin_cases round <;> norm_num [Finalization.isFinal, Fin.ext_iff]

theorem nonfinal_flag {p : Nat} [Fact p.Prime]
    {setup : Table (ZMod p) (fields 4)} {w : Nat → ZMod p}
    {input : Finalization.Input} {output : Finalization.Output}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (mapping : Finalization.WordMapping input output w)
    (interface : Finalization.NonFinalAssumptions input output w) : w 152 = 0 := by
  have flag := finalization_flag h mapping interface.roundMask
  rw [nonfinal_reference interface] at flag
  exact flag

/-- Every chaining-state limb is preserved by its actual write equation when
    final XOR is disabled. No range or XOR-table assumptions are needed. -/
theorem chaining_preserved {p : Nat} [Fact p.Prime]
    {setup : Table (ZMod p) (fields 4)} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (disabled : w 152 = 0) :
    Preparation.words w Finalization.stateWrites = Preparation.words w Variables.stateReads := by
  have limbs (i : Fin 8) : w (7 + 4 * i.val) = w (5 + 4 * i.val) ∧
      w (8 + 4 * i.val) = w (6 + 4 * i.val) := by
    have low := Verification.assertion_of_holds h
      ⟨153 + 4 * i.val, by rw [constraint_count]; have size := i.isLt; omega⟩
    have high := Verification.assertion_of_holds h
      ⟨155 + 4 * i.val, by rw [constraint_count]; have size := i.isLt; omega⟩
    fin_cases i
    all_goals simp [importedConstraints, FlatOperation.constraints, Expression.eval,
      Verification.environment, disabled] at low high
    all_goals constructor
    all_goals solve | linear_combination -low | linear_combination -high
  apply Vector.ext
  intro i hi
  have equal := limbs ⟨i, hi⟩
  simp [Preparation.words, Finalization.stateWrites, Variables.stateReads, equal.1, equal.2]

theorem nonfinal_soundness {p : Nat} [Fact p.Prime] :
    (Finalization.circuitModel (p := p)).SoundnessUnder (Finalization.NonFinalAssumptions (p := p))
      Finalization.spec := by
  intro input output w ⟨interface, holds, mapping⟩
  unfold Finalization.spec
  rw [nonfinal_reference interface]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [mapping.output, mapping.state]
  exact chaining_preserved holds (nonfinal_flag holds mapping interface)

/-- One shared soundness claim covers all full/reduced final and non-final rounds. -/
theorem finalization_soundness {p : Nat} [Fact p.Prime] (hp : 65536 ≤ p)
    (compatible : 64 * (-31457280 : ZMod p) = 1) :
    (Finalization.circuitModel (p := p)).SoundnessUnder (Finalization.InterfaceAssumptions (p := p))
      Finalization.spec := by
  intro input output w ⟨interface, holds, mapping⟩
  have flag := finalization_flag holds mapping interface.roundMask
  unfold Finalization.spec
  split_ifs with final
  · have enabled : w 152 = 1 := by simpa only [if_pos final] using flag
    rw [mapping.output, mapping.chaining, mapping.extended]
    exact final_xor_writes hp compatible holds enabled
  · have disabled : w 152 = 0 := by simpa only [if_neg final] using flag
    rw [mapping.output, mapping.state]
    exact chaining_preserved holds disabled

end Airbender.Blake2Round.Proofs
