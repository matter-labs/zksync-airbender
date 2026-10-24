import Airbender.Proofs.Blake2G.NativeCall
import Airbender.Proofs.Blake2G.Control
import Airbender.Review.Circuits.Blake2G.Protocol
import Airbender.Proofs.BabyBear

namespace Airbender.Blake2G.Proofs
open Trace Arithmetic
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

/-- The actual native quadratic excludes the controller table's active fallback
rows. The table itself retains its deterministic values for every key. -/
theorem successful_control {w : Nat → ZMod babyBearModulus}
    (core : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints (setupTable Control.controllerRows))) :
    (w 3 + w 0 - w 5) * (16 * (w 3 + w 0 - w 5) - 1280 + 3 * w 5) = 0 := by
  have guard := Verification.assertion_of_holds core ⟨11, by rw [constraint_count]; decide⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval,
    Verification.environment, -mul_eq_zero] at guard
  convert guard using 1
  ring

private theorem controller_guard : ∀ key : Fin 512, 256 ≤ key.val →
    let read : ZMod babyBearModulus := key.val - 256
    let written : ZMod babyBearModulus := (Control.controllerRows key)[0]
    (read + 1 - written) * (16 * (read + 1 - written) - 1280 + 3 * written) = 0 →
    (key.val - 256) % 128 < (if (key.val - 256) / 128 = 0 then 80 else 56) := by
  decide +kernel

/-- Every active native G controller has a successful position. The canonical
read bound is obtained from initialized shared memory by the caller theorem. -/
theorem successful_position {w : Nat → ZMod babyBearModulus}
    (core : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints (setupTable Control.controllerRows)))
    (active : w 0 = 1) (readBound : (w 3).val < 65536) :
    ∃ reduced : Bool, ∃ index : Fin (callCount reduced),
      (readToken w importedConstraintsMemoryPorts[8]).word = controlAt reduced index.val := by
  obtain ⟨key, encoded, outputs⟩ := Control.Proofs.control_columns (by decide) core
  have field : ((w 3).val + 256 : Nat) = key.val := by
    apply bounded_nat_eq (F := ZMod babyBearModulus) (p := babyBearModulus)
      (Nat.lt_trans (Nat.add_lt_add_right readBound 256) (by decide))
      (Nat.lt_trans key.isLt (by decide))
    simpa only [Nat.cast_add, ZMod.natCast_zmod_val, Nat.cast_ofNat, active, mul_one] using encoded
  have lower : 256 ≤ key.val := by omega
  have readField : w 3 = ((key.val - 256 : Nat) : ZMod babyBearModulus) := by
    have value : (w 3).val = key.val - 256 := by omega
    rw [← value, ZMod.natCast_zmod_val]
  have written : w 5 = ((Control.controllerRows key)[0] : ZMod babyBearModulus) := outputs 0
  have guard := successful_control core
  rw [active, readField, written] at guard
  have support := controller_guard key lower (by simpa [Nat.cast_sub lower] using guard)
  have size : key.val - 256 < 256 := by have := key.isLt; omega
  have raw : (readToken w importedConstraintsMemoryPorts[8]).word = ⟨key.val - 256, 0⟩ := by
    rw [(Call.Proofs.controller_words w).1]
    have high := (control_high_zero core).1
    simp only [high, ZMod.val_zero]
    congr 1
    omega
  by_cases full : key.val - 256 < 128
  · have counter : key.val - 256 < 80 := by
      simpa only [Nat.mod_eq_of_lt full, Nat.div_eq_of_lt full, ↓reduceIte] using support
    refine ⟨false, ⟨key.val - 256, counter⟩, ?_⟩
    simpa only [controlAt, callCount, Bool.false_eq_true, ↓reduceIte, Fin.val_mk,
      Nat.mod_eq_of_lt counter, Nat.zero_add] using raw
  · have division : (key.val - 256) / 128 = 1 := by omega
    have remainder : (key.val - 256) % 128 = key.val - 384 := by omega
    have counter : key.val - 384 < 56 := by simpa [division, remainder] using support
    refine ⟨true, ⟨key.val - 384, counter⟩, ?_⟩
    rw [raw]
    simp only [controlAt, callCount, ↓reduceIte, Nat.mod_eq_of_lt counter]
    congr 1
    omega

/-- The appended inverse equation enforces distinct block bases at every native
position, including calls whose counter was loaded or otherwise computed. -/
theorem successful_bases {w : Nat → ZMod babyBearModulus}
    (core : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints (setupTable Control.controllerRows)))
    (active : w 0 = 1)
    (bounds : (Native.statePointer w).Bounded ∧ (Native.messagePointer w).Bounded) :
    (Native.statePointer w).toBitVec ≠ (Native.messagePointer w).toBitVec := by
  intro same
  have words : Native.statePointer w = Native.messagePointer w := by
    apply Word.eq_of_value bounds.1 bounds.2
    have values := congrArg BitVec.toNat same
    simpa only [Word.toBitVec_toNat bounds.1, Word.toBitVec_toNat bounds.2] using values
  have pointers : Native.statePointer w = ⟨(w 13).val, (w 14).val⟩ ∧
      Native.messagePointer w = ⟨(w 31).val, (w 32).val⟩ := by
    simp [Native.statePointer, Native.messagePointer, Delegation.Row.readWord,
      Delegation.Row.ports, readToken, MemoryPort.readCode, MemoryToken.word, WordColumns.code,
      WordColumns.evaluate, importedConstraintsMemoryPorts]
  rw [pointers.1, pointers.2] at words
  have low : w 13 = w 31 := (ZMod.val_injective babyBearModulus) (congrArg Word.lo words)
  have high : w 14 = w 32 := (ZMod.val_injective babyBearModulus) (congrArg Word.hi words)
  have guard := Verification.assertion_of_holds core ⟨12, by rw [constraint_count]; decide⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval,
    Verification.environment, low, high, active] at guard

end Airbender.Blake2G.Proofs
