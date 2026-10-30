import Airbender.Proofs.Keccak.SplitScheduleControl
import Airbender.Proofs.Keccak.SplitChiReferenceEffect
import Airbender.Proofs.Trace.SailCells

namespace Airbender.Keccak.Split.Native.Proofs
open Trace Trace.Proofs Reference.RiscV.Sail Reference.Sail
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 1600000
variable [Fact babyBearModulus.Prime]

/-- The actual native control port addresses architectural register ten. -/
theorem chi5_control_port_address (cached : Bool) (w : Nat → ZMod babyBearModulus) :
    (chi5ControlPort cached).address.code w =
      (Cell.register 10).addressCode := by
  cases cached <;> rfl

/-- A reference control read identifies the unique actual native blessed call. -/
theorem chi5_call_control_binding (cached : Bool) (w : Nat → ZMod babyBearModulus)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (if cached then Chi5Cached.clockConstraints chi5FixedTable else Chi5.clockConstraints chi5FixedTable))
    (active : w 0 = 1) (index : Fin 361) (before : State)
    (arguments : ArgumentsAt index.val before)
    (observed : ∃ cell : Cell, cell.addressCode = (chi5ControlPort cached).address.code w ∧
      cell.read before = .ok (readToken w (chi5ControlPort cached)).word.toBitVec before) :
    kindAt index.val = .chi5 ∧
      (chi5ControllerRow cached w)[0] = (controlAt index.val : ZMod babyBearModulus) ∧
      (chi5ControllerRow cached w)[2] = (bump (controlAt index.val) : ZMod babyBearModulus) ∧
      (∀ lane : Fin 5, (chi5ControllerRow cached w)[3 + lane.val] =
        ((Call.slots index)[lane.val].val : ZMod babyBearModulus)) := by
  obtain ⟨actual, kind, control, next, slots, _⟩ := chi5_native_controller_schedule cached w holds active
  have codes := chi5_control_port_codes cached w holds
  have small : controlAt actual.val < babyBearModulus :=
    lt_of_lt_of_le (split_control_limb_bounds actual).1 (by decide)
  have nativeBits : (readToken w (chi5ControlPort cached)).word.toBitVec =
      BitVec.ofNat 32 (controlAt actual.val) := by
    change BitVec.ofNat 32 ((Nat.unpair ((chi5ControlPort cached).readCode w)).1 +
      Arithmetic.limbBase * (Nat.unpair ((chi5ControlPort cached).readCode w)).2) = _
    rw [codes.1, control, ZMod.val_natCast_of_lt small]
    simp only [Nat.unpair_pair, mul_zero, add_zero]
  obtain ⟨cell, code, read⟩ := observed
  have address : (chi5ControlPort cached).address.code w = (Cell.register 10).addressCode := by
    exact chi5_control_port_address cached w
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
  exact ⟨kind, control, next, slots⟩

end Airbender.Keccak.Split.Native.Proofs
