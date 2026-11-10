import Airbender.Proofs.Keccak.SplitScheduleControl
import Airbender.Proofs.Keccak.SplitThetaPortEnumeration
import Airbender.Proofs.Keccak.SplitChiMemoryEffect
import Airbender.Proofs.Trace.SailCells

namespace Airbender.Keccak.Split.Native.Proofs
open Trace Trace.Proofs Reference.RiscV.Sail Reference.Sail
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
variable [Fact babyBearModulus.Prime]

/-- The actual native control port addresses architectural register ten. -/
theorem theta_control_port_address (cached : Bool) (w : Nat → ZMod babyBearModulus) :
    (thetaControlPort cached).address.code w =
      (Cell.register 10).addressCode := by
  cases cached <;> rfl

/-- A reference control read identifies the unique actual native blessed call. -/
theorem theta_call_control_binding (cached : Bool) (w : Nat → ZMod babyBearModulus)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (if cached then ThetaRhoCached.clockConstraints thetaRhoFixedTable else ThetaRho.clockConstraints thetaRhoFixedTable))
    (active : w 0 = 1) (index : Fin 361) (before : State)
    (arguments : ArgumentsAt index.val before)
    (observed : ∃ cell : Cell, cell.addressCode = (thetaControlPort cached).address.code w ∧
      cell.read before = .ok (readToken w (thetaControlPort cached)).word.toBitVec before) :
    kindAt index.val = .thetaRho ∧
      (thetaQueryRow cached w 9)[0] = (controlAt index.val : ZMod babyBearModulus) ∧
      (thetaQueryRow cached w 9)[2] = (bump (controlAt index.val) : ZMod babyBearModulus) ∧
      (∀ lane : Fin 7, (thetaQueryRow cached w 0)[1 + lane.val] =
        ((Call.slots index)[lane.val].val : ZMod babyBearModulus)) ∧
      ∀ selected : Fin 5, thetaColumnFlag cached w selected = if selected.val = index.val % 5 then 1 else 0 := by
  obtain ⟨actual, kind, control, next, selected⟩ := theta_native_controller_schedule cached w holds active
  have slots := theta_native_slots cached w holds active actual control
  have codes := theta_control_port_codes cached w holds
  have small : controlAt actual.val < babyBearModulus :=
    lt_of_lt_of_le (split_control_limb_bounds actual).1 (by decide)
  have nativeBits : (readToken w (thetaControlPort cached)).word.toBitVec =
      BitVec.ofNat 32 (controlAt actual.val) := by
    change BitVec.ofNat 32 ((Nat.unpair ((thetaControlPort cached).readCode w)).1 +
      Arithmetic.limbBase * (Nat.unpair ((thetaControlPort cached).readCode w)).2) = _
    rw [codes.1, control, ZMod.val_natCast_of_lt small]
    simp only [Nat.unpair_pair, mul_zero, add_zero]
  obtain ⟨cell, code, read⟩ := observed
  have address : (thetaControlPort cached).address.code w = (Cell.register 10).addressCode := by
    exact theta_control_port_address cached w
  have sameCell := cell_address_injective (code.trans address)
  rw [sameCell, nativeBits] at read
  obtain ⟨controlWord, pointer, controlRead, _, controlWordEq, _, _⟩ := arguments
  rw [controlWordEq] at controlRead
  have bits := (EStateM.Result.ok.inj (read.symm.trans controlRead)).1
  have numeric := congrArg BitVec.toNat bits
  have actualBound : controlAt actual.val < 2 ^ 32 :=
    lt_of_lt_of_le (split_control_limb_bounds actual).1 (by decide)
  have expectedBound : controlAt index.val < 2 ^ 32 :=
    lt_of_lt_of_le (split_control_limb_bounds index).1 (by decide)
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt actualBound,
    Nat.mod_eq_of_lt expectedBound] at numeric
  have same := Split.Proofs.control_injective numeric
  subst actual
  exact ⟨kind, control, next, slots, selected⟩

end Airbender.Keccak.Split.Native.Proofs
