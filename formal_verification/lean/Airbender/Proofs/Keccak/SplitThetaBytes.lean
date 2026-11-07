import Airbender.Proofs.Keccak.SplitThetaNativeQueries
import Airbender.Review.Trace.Workers.Keccak.SplitNative

namespace Airbender.Keccak.Split.Native.Proofs
open Trace
set_option warningAsError true
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
variable [Fact babyBearModulus.Prime]

/-- One actual native theta/rho read or write limb, including readonly refreshes. -/
def thetaLaneLimb (cached writing : Bool) (w : Nat → ZMod babyBearModulus)
    (lane : Fin 7) (limb : Fin 4) : ZMod babyBearModulus :=
  let ports := (⟨.thetaRho, w⟩ : Row babyBearModulus).ports cached
  let port := ports[2 + 2 * lane.val + limb.val / 2]'(by
    have size : ports.size = 16 := by cases cached <;> rfl
    rw [size]
    have := lane.isLt
    have := limb.isLt
    omega)
  let columns := if writing then port.writeValue.getD port.readValue else port.readValue
  (columns.evaluate w)[limb.val % 2]'(Nat.mod_lt _ (by decide))

/-- An actual state byte in one of the forty native XOR/split queries. -/
def thetaStateByte (cached : Bool) (w : Nat → ZMod babyBearModulus)
    (lane : Fin 5) (digit : Fin 8) : ZMod babyBearModulus :=
  (thetaRhoQueryEntry cached ⟨10 + 8 * lane.val + digit.val, by omega⟩)[0].eval
    (Verification.environment w)

/-- An actual previous-column byte in one of the eight native XOR queries. -/
def thetaPreviousByte (cached : Bool) (w : Nat → ZMod babyBearModulus) (digit : Fin 8) : ZMod babyBearModulus :=
  (thetaRhoQueryEntry cached ⟨1 + digit.val, by omega⟩)[0].eval (Verification.environment w)

/-- An actual rotated next-column byte in the native XOR query. -/
def thetaRotatedByte (cached : Bool) (w : Nat → ZMod babyBearModulus) (digit : Fin 8) : ZMod babyBearModulus :=
  (thetaRhoQueryEntry cached ⟨1 + digit.val, by omega⟩)[1].eval (Verification.environment w)

/-- The actual shared D byte produced by the native XOR query. -/
def thetaDByte (cached : Bool) (w : Nat → ZMod babyBearModulus) (digit : Fin 8) : ZMod babyBearModulus :=
  (thetaRhoQueryEntry cached ⟨1 + digit.val, by omega⟩)[2].eval (Verification.environment w)

/-- An actual low or high fragment produced by the native XOR/split query. -/
def thetaFragmentByte (cached high : Bool) (w : Nat → ZMod babyBearModulus)
    (lane : Fin 5) (digit : Fin 8) : ZMod babyBearModulus :=
  (thetaRhoQueryEntry cached ⟨10 + 8 * lane.val + digit.val, by omega⟩)[if high then 4 else 3]'(by split <;> decide) |>.eval
    (Verification.environment w)

/-- The actual shift expression shared by all eight bytes of one native state lane. -/
def thetaRotationShift (cached : Bool) (w : Nat → ZMod babyBearModulus) (lane : Fin 5) : ZMod babyBearModulus :=
  (thetaRhoQueryEntry cached ⟨10 + 8 * lane.val, by omega⟩)[2].eval (Verification.environment w)

/-- All actual state operands have canonical byte values. -/
theorem theta_state_byte_bound (cached : Bool) (w : Nat → ZMod babyBearModulus)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (if cached then ThetaRhoCached.clockConstraints thetaRhoFixedTable
        else ThetaRho.clockConstraints thetaRhoFixedTable)) (lane : Fin 5) (digit : Fin 8) :
    (thetaStateByte cached w lane digit).val < 256 := by
  have facts := theta_rho_native_split_queries cached w holds ⟨8 * lane.val + digit.val, by omega⟩
  simpa only [thetaStateByte, Vector.getElem_map, Nat.add_assoc] using facts.1

/-- The previous-column, rotated-column and D operands all have canonical byte values. -/
theorem theta_d_operand_bounds (cached : Bool) (w : Nat → ZMod babyBearModulus)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (if cached then ThetaRhoCached.clockConstraints thetaRhoFixedTable
        else ThetaRho.clockConstraints thetaRhoFixedTable)) (digit : Fin 8) :
    (thetaPreviousByte cached w digit).val < 256 ∧ (thetaRotatedByte cached w digit).val < 256 ∧
      (thetaDByte cached w digit).val < 256 := by
  have facts := theta_rho_native_xor_queries cached w holds digit
  simpa only [thetaPreviousByte, thetaRotatedByte, thetaDByte, Vector.getElem_map] using
    And.intro facts.1 (And.intro facts.2.1 facts.2.2.1)

/-- The actual native D byte is the XOR of its actual previous and rotated column bytes. -/
theorem theta_d_byte_operation (cached : Bool) (w : Nat → ZMod babyBearModulus)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (if cached then ThetaRhoCached.clockConstraints thetaRhoFixedTable
        else ThetaRho.clockConstraints thetaRhoFixedTable)) (digit : Fin 8) :
    (thetaDByte cached w digit).val =
      (thetaPreviousByte cached w digit).val ^^^ (thetaRotatedByte cached w digit).val := by
  simpa only [thetaPreviousByte, thetaRotatedByte, thetaDByte, Vector.getElem_map] using
    (theta_rho_native_xor_queries cached w holds digit).2.2.2.1

/-- Every actual state fragment query consumes the same native D byte. -/
theorem theta_d_query_shared (cached : Bool) (w : Nat → ZMod babyBearModulus)
    (lane : Fin 5) (digit : Fin 8) :
    (thetaRhoQueryEntry cached ⟨10 + 8 * lane.val + digit.val, by omega⟩)[1].eval
      (Verification.environment w) = thetaDByte cached w digit := by
  cases cached <;> fin_cases lane <;> fin_cases digit <;> rfl

/-- All eight actual fragment queries share their native lane's shift expression. -/
theorem theta_shift_query_shared (cached : Bool) (w : Nat → ZMod babyBearModulus)
    (lane : Fin 5) (digit : Fin 8) :
    (thetaRhoQueryEntry cached ⟨10 + 8 * lane.val + digit.val, by omega⟩)[2].eval
      (Verification.environment w) = thetaRotationShift cached w lane := by
  cases cached <;> fin_cases lane <;> fin_cases digit <;> rfl

/-- Both actual native fragments have canonical byte values. -/
theorem theta_fragment_byte_bound (cached high : Bool) (w : Nat → ZMod babyBearModulus)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (if cached then ThetaRhoCached.clockConstraints thetaRhoFixedTable
        else ThetaRho.clockConstraints thetaRhoFixedTable)) (lane : Fin 5) (digit : Fin 8) :
    (thetaFragmentByte cached high w lane digit).val < 256 := by
  have facts := theta_rho_native_split_queries cached w holds ⟨8 * lane.val + digit.val, by omega⟩
  cases high
  · simpa only [thetaFragmentByte, Vector.getElem_map, Nat.add_assoc, Bool.false_eq_true, ↓reduceIte] using facts.2.2.2.1
  · simpa only [thetaFragmentByte, Vector.getElem_map, Nat.add_assoc, ↓reduceIte] using facts.2.2.2.2.1

/-- The actual native rotation shift stays in the complete zero-through-seven domain. -/
theorem theta_rotation_shift_bound (cached : Bool) (w : Nat → ZMod babyBearModulus)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (if cached then ThetaRhoCached.clockConstraints thetaRhoFixedTable
        else ThetaRho.clockConstraints thetaRhoFixedTable)) (lane : Fin 5) :
    (thetaRotationShift cached w lane).val < 8 := by
  simpa only [thetaRotationShift, Vector.getElem_map] using
    (theta_rho_native_split_queries cached w holds ⟨8 * lane.val, by omega⟩).2.2.1

/-- Every actual fragment query has the exact shared-D and shared-shift meaning. -/
theorem theta_fragment_byte_operation (cached : Bool) (w : Nat → ZMod babyBearModulus)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (if cached then ThetaRhoCached.clockConstraints thetaRhoFixedTable
        else ThetaRho.clockConstraints thetaRhoFixedTable)) (lane : Fin 5) (digit : Fin 8) :
    (thetaFragmentByte cached false w lane digit).val =
      ((thetaStateByte cached w lane digit).val ^^^ (thetaDByte cached w digit).val) *
        2 ^ (thetaRotationShift cached w lane).val % 256 ∧
      (thetaFragmentByte cached true w lane digit).val =
        ((thetaStateByte cached w lane digit).val ^^^ (thetaDByte cached w digit).val) /
          2 ^ (8 - (thetaRotationShift cached w lane).val) := by
  have facts := theta_rho_native_split_queries cached w holds ⟨8 * lane.val + digit.val, by omega⟩
  have low := facts.2.2.2.2.2.1
  have high := facts.2.2.2.2.2.2.1
  simp only [Vector.getElem_map] at low high
  have sharedD := theta_d_query_shared cached w lane digit
  have sharedShift := theta_shift_query_shared cached w lane digit
  simp only [Nat.add_assoc] at sharedD sharedShift
  rw [sharedD, sharedShift] at low high
  simpa only [thetaFragmentByte, thetaStateByte, Nat.add_assoc, Bool.false_eq_true, ↓reduceIte] using
    And.intro low high

omit [Fact babyBearModulus.Prime] in
/-- Both native readonly lanes preserve every complete memory limb. -/
theorem theta_readonly_limb (cached : Bool) (w : Nat → ZMod babyBearModulus)
    (lane : Fin 2) (limb : Fin 4) :
    thetaLaneLimb cached true w ⟨5 + lane.val, by omega⟩ limb =
      thetaLaneLimb cached false w ⟨5 + lane.val, by omega⟩ limb := by
  cases cached <;> fin_cases lane <;> fin_cases limb <;> rfl

end Airbender.Keccak.Split.Native.Proofs
