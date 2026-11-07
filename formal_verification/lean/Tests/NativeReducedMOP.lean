import Airbender.Review.Circuits.ReducedMachine.MOPTheorems
import Airbender.Proofs.ReducedMachine.NativePool

namespace Tests.NativeReducedMOP
open Airbender Arithmetic ReducedMachine Native Verification
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- Minor order is ADD/MUL/SUB, distinct from the enum order ADD/SUB/MUL. -/
theorem masks_and_minors :
    (#[MOPMode.add.mask,MOPMode.sub.mask,MOPMode.mul.mask] : Array Nat) = #[34819,133123,67587] ∧
    NativeMOPSelectorProofs.bit .add 15 = 1 ∧ NativeMOPSelectorProofs.bit .mul 16 = 1 ∧
    NativeMOPSelectorProofs.bit .sub 17 = 1 := by decide +kernel

/-- Boundary references distinguish field arithmetic from RV32 wrapping. -/
theorem field_boundaries :
    (MOPMode.add.field 2147483646 1).val = 0 ∧
    (MOPMode.sub.field 0 1).val = 2147483646 ∧
    (MOPMode.mul.field 2147483646 2147483646).val = 1 ∧
    (MOPMode.mul.field 4294967295 4294967295).val = 1 := by decide +kernel

section ConditionalNative
variable {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup))

include holds

/-- Full native constraints derive the result from explicit source fixtures;
    no result/range or actual Sail read is assumed. -/
theorem add_modulus_wrap (mask : w 12 = 34819)
    (source : sourceWord w = ⟨65534,32767⟩) (second : registerOperandWord w = ⟨1,0⟩) :
    (mopOutputWord w).value = 0 := by
  have result := (mop_arithmetic holds .add mask).result
  rw [source,second] at result
  exact result.trans (by decide +kernel)

theorem sub_zero_borrow (mask : w 12 = 133123)
    (source : sourceWord w = ⟨0,0⟩) (second : registerOperandWord w = ⟨1,0⟩) :
    (mopOutputWord w).value = 2147483646 := by
  have result := (mop_arithmetic holds .sub mask).result
  rw [source,second] at result
  exact result.trans (by decide +kernel)

/-- Both full RV32 sources exceed the field modulus; their native field
    reduction is retained, without imposing a false source < p restriction. -/
theorem mul_full_word (mask : w 12 = 67587)
    (source : sourceWord w = ⟨65535,65535⟩) (second : registerOperandWord w = ⟨65535,65535⟩) :
    (mopOutputWord w).value = 1 := by
  have result := (mop_arithmetic holds .mul mask).result
  rw [source,second] at result
  exact result.trans (by decide +kernel)

theorem modulus_output_rejected (mode : MOPMode) (mask : w 12 = (mode.mask : ZMod mersenne31Modulus))
    (bad : mopOutputWord w = ⟨65535,32767⟩) : False := by
  have bound := (mop_arithmetic holds mode mask).canonical
  rw [bad] at bound
  norm_num [Word.value,limbBase,mersenne31Modulus] at bound

/-- The high-bit exclusion follows canonical output, not a desired bound. -/
theorem high_bit_rejected (mode : MOPMode) (mask : w 12 = (mode.mask : ZMod mersenne31Modulus)) :
    (mopOutputWord w).hi < 32768 := by
  have bound := (mop_arithmetic holds mode mask).canonical
  simp only [Word.value,limbBase,mersenne31Modulus] at bound
  omega

/-- Discarded writes still satisfy all arithmetic/canonical candidate checks. -/
theorem discarded_write (mode : MOPMode) (mask : w 12 = (mode.mask : ZMod mersenne31Modulus))
    (zero : rdZeroFlag w = 1) : rdWrite w = #v[0,0] ∧ (mopOutputWord w).value < mersenne31Modulus := by
  have actual := mop_arithmetic holds mode mask
  exact ⟨by rw [actual.written]; simp [zero,mopCandidate],actual.canonical⟩

theorem ram_second_source_rejected (mode : MOPMode) (mask : w 12 = (mode.mask : ZMod mersenne31Modulus)) :
    w 88 ≠ 0 := by
  rw [(mop_arithmetic holds mode mask).secondPort.2.2]
  decide

end ConditionalNative

-- Independent partial assignments for actual polynomial checks ONLY. These
-- satisfy neither all117 native equations nor all22 lookups by this theorem.
private def sample (mode : MOPMode) (column : Nat) : ZMod mersenne31Modulus :=
  let source : Nat × Nat := match mode with | .add => (65534,32767) | .sub => (0,0) | .mul => (65535,65535)
  let second : Nat × Nat := match mode with | .mul => (65535,65535) | _ => (1,0)
  let output : Nat × Nat := match mode with | .sub => (65534,32767) | .mul => (1,0) | .add => (0,0)
  match column with
  | 12 => mode.mask | 18 | 28 | 63 | 95 => 1
  | 32 => if mode = .add then 1 else 0
  | 33 => if mode = .mul then 1 else 0
  | 34 => if mode = .sub then 1 else 0
  | 35 => source.1 | 36 => source.2
  | 37 | 47 => second.1 | 38 | 48 => second.2
  | 61 | 84 => output.1 | 62 | 85 => output.2
  | 69 => output.1+1 | 70 => output.2+32768
  | 83 => match mode with | .add => 2147483646 | .sub => 0 | .mul => 1
  | _ => 0

private def polynomialValue (mode : MOPMode) (index : Fin 117) : ZMod mersenne31Modulus :=
  ((FlatOperation.constraints (importedConstraints setupTable)).get index).eval (environment (sample mode))
  where setupTable : Table (ZMod mersenne31Modulus) (fields 4) := NativeFixed.table

/-- Positive slices check actual multiplication/arithmetic/canonical-borrow
    equations for all three independent boundary assignments, without any
    native acceptance or architectural execution claim. -/
theorem native_arithmetic_slices (mode : MOPMode) (slot : Fin 7) :
    polynomialValue mode (#v[(49 : Fin 117),50,51,52,53,74,75][slot]) = 0 := by
  cases mode <;> fin_cases slot <;> decide +kernel

theorem slice_ranges (mode : MOPMode) :
    (mopOutputWord (sample mode)).Bounded ∧
    (⟨(sample mode 69).val,(sample mode 70).val⟩ : Word).Bounded := by
  cases mode <;> simp only [Word.Bounded] <;> decide +kernel

end Tests.NativeReducedMOP
