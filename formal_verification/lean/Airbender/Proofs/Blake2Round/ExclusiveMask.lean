import Airbender.Proofs.Blake2Round.Control
import Airbender.Review.Blake2Round.Memory

namespace Airbender.Blake2Round.Proofs
open Arithmetic
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000

theorem exclusive_mask [Fact p.Prime] (hp : 8192 ≤ p)
    {setup : Table (ZMod p) (fields 4)} {w : Nat → ZMod p}
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (flags : Fin 8) (round : Fin 10)
    (read : (w Variables.controlReadHi).val = flags.val + 8 * 2 ^ round.val) :
    Memory.RoundMask w round := by
  have bits (i : Fin 13) : (w Variables.controlBits[i]).val ≤ 1 :=
    boolean_val (Control.Proofs.control_bits holds i)
  have b0 := bits 0; have b1 := bits 1; have b2 := bits 2
  have b3 := bits 3; have b4 := bits 4; have b5 := bits 5
  have b6 := bits 6; have b7 := bits 7; have b8 := bits 8
  have b9 := bits 9; have b10 := bits 10; have b11 := bits 11; have b12 := bits 12
  have equation := Verification.assertion_of_holds holds ⟨1, by rw [constraint_count]; decide⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval,
    Verification.environment] at equation
  let encoded := (w 139).val + 2 * (w 140).val + 4 * (w 141).val +
    8 * (w 142).val + 16 * (w 143).val + 32 * (w 144).val +
    64 * (w 145).val + 128 * (w 146).val + 256 * (w 147).val +
    512 * (w 148).val + 1024 * (w 149).val + 2048 * (w 150).val + 4096 * (w 151).val
  have field : (encoded : ZMod p) = w Variables.controlReadHi := by
    simp only [encoded, Variables.controlReadHi, Nat.cast_add, Nat.cast_mul, ZMod.natCast_zmod_val]
    linear_combination equation
  change (w 139).val ≤ 1 at b0
  change (w 140).val ≤ 1 at b1
  change (w 141).val ≤ 1 at b2
  change (w 142).val ≤ 1 at b3
  change (w 143).val ≤ 1 at b4
  change (w 144).val ≤ 1 at b5
  change (w 145).val ≤ 1 at b6
  change (w 146).val ≤ 1 at b7
  change (w 147).val ≤ 1 at b8
  change (w 148).val ≤ 1 at b9
  change (w 149).val ≤ 1 at b10
  change (w 150).val ≤ 1 at b11
  change (w 151).val ≤ 1 at b12
  have bound : encoded < p := by dsimp [encoded]; omega
  have natural : encoded = flags.val + 8 * 2 ^ round.val := by
    rw [← read, ← field, ZMod.val_natCast_of_lt bound]
  dsimp [encoded] at natural
  have flagsBound := flags.isLt
  have column (i : Fin 10) : Variables.roundBits[i] = 142 + i.val := by
    fin_cases i <;> rfl
  intro i
  rw [column i]
  apply ZMod.val_injective
  have prime := (Fact.out : p.Prime).one_lt
  letI : Fact (1 < p) := ⟨prime⟩
  fin_cases round <;> fin_cases i
  all_goals norm_num only [Fin.val_mk] at natural
  all_goals norm_num only [Fin.val_mk, Nat.reduceAdd, Fin.mk.injEq, ZMod.val_one, ZMod.val_zero]
  all_goals simp only [ite_true, ite_false, ZMod.val_one, ZMod.val_zero]
  all_goals omega

end Airbender.Blake2Round.Proofs
