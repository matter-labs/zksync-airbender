import Airbender.Review.Circuits.Blake2Worker.ControlTheorems

namespace Tests.NativeBlake2Worker
open Airbender Airbender.Blake2Worker Airbender.Blake2Worker.Native Airbender.Verification
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

variable {setup : Table (ZMod mersenne31Modulus) (fields 4)} {w : Nat → ZMod mersenne31Modulus}

theorem native_geometry : constraintsABI.traceLength = 1048576 ∧
    constraintsABI.registers.size = 3 ∧ constraintsABI.processingAux = 1064 := by decide

theorem processor_distinct_from_caller : constraintsABI.multiplicity = 0 ∧
    constraintsABI.offsetHigh = 1 ∧ constraintsABI.writeTime = #v[740,741] := by decide

theorem readonly_registers_retained : (constraintsABI.registers[0]!).access.writeValue = none ∧
    (constraintsABI.registers[1]!).access.writeValue = none := by decide

theorem last_state_write : ((constraintsABI.registers[0]!).indirects[23]!).offset = 92 ∧
    ((constraintsABI.registers[0]!).indirects[23]!).writeValue.isSome = true := by decide

theorem last_message_read : ((constraintsABI.registers[1]!).indirects[15]!).offset = 60 ∧
    ((constraintsABI.registers[1]!).indirects[15]!).writeValue = none := by decide

theorem high_control_rejected
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints setup))
    (bad : controlHigh w = 8192) : False := by
  have bound := (control_effects (setup := setup) (w := w) holds).inputBounded
  omega

theorem uncleared_low_rejected
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints setup))
    (bad : w 136 ≠ 0) : False :=
  bad (control_effects (setup := setup) (w := w) holds).lowCleared

private def sample (high output : Nat) : Nat → ZMod mersenne31Modulus := fun i =>
  if i = 135 then high else if i = 137 then output
  else if 138 ≤ i ∧ i < 151 then ((high / 2^(i-138) % 2 : Nat) : ZMod mersenne31Modulus)
  else 0

private def polynomialValue (setup : Table (ZMod mersenne31Modulus) (fields 4))
    (high output : Nat) (slot : Fin 16) : ZMod mersenne31Modulus :=
  if h : slot.val < 13 then
    ((FlatOperation.constraints (constraintsBlock0 setup)).get ⟨slot.val,by change slot.val < 64; omega⟩).eval
      (environment (sample high output))
  else
    ((FlatOperation.constraints (constraintsBlock4 setup)).get ⟨45+(slot.val-13),by change _ < 64; omega⟩).eval
      (environment (sample high output))

/-- These positive checks cover only the13 actual Boolean equations and3
    actual x12 linear equations, not complete352-equation/296-lookup witnesses.
    Zero/multiple round flags here are not established native defects. -/
theorem zero_control_slice (setup : Table (ZMod mersenne31Modulus) (fields 4)) (slot : Fin 16) :
    polynomialValue setup 0 0 slot = 0 := by
  fin_cases slot <;> dsimp [polynomialValue,constraintsBlock0,constraintsBlock4,FlatOperation.constraints,Expression.eval,environment] <;> decide +kernel

theorem first_round_slice (setup : Table (ZMod mersenne31Modulus) (fields 4)) (slot : Fin 16) :
    polynomialValue setup 8 16 slot = 0 := by
  fin_cases slot <;> dsimp [polynomialValue,constraintsBlock0,constraintsBlock4,FlatOperation.constraints,Expression.eval,environment] <;> decide +kernel

theorem final_round_slice (setup : Table (ZMod mersenne31Modulus) (fields 4)) (slot : Fin 16) :
    polynomialValue setup 4096 0 slot = 0 := by
  fin_cases slot <;> dsimp [polynomialValue,constraintsBlock0,constraintsBlock4,FlatOperation.constraints,Expression.eval,environment] <;> decide +kernel

theorem multiple_round_slice (setup : Table (ZMod mersenne31Modulus) (fields 4)) (slot : Fin 16) :
    polynomialValue setup 24 48 slot = 0 := by
  fin_cases slot <;> dsimp [polynomialValue,constraintsBlock0,constraintsBlock4,FlatOperation.constraints,Expression.eval,environment] <;> decide +kernel

theorem mode_flags_slice (setup : Table (ZMod mersenne31Modulus) (fields 4)) (slot : Fin 16) :
    polynomialValue setup 7 7 slot = 0 := by
  fin_cases slot <;> dsimp [polynomialValue,constraintsBlock0,constraintsBlock4,FlatOperation.constraints,Expression.eval,environment] <;> decide +kernel

end Tests.NativeBlake2Worker
