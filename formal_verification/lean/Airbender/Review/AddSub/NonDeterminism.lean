import Airbender.Review.AddSub.Model

namespace Airbender.AddSub.NonDeterminism
open Airbender.Arithmetic
open Airbender.Reference.RiscV

/-- Fixed native state for CSRRW x0, 0x7C0, rs1. Source/hint data has no proved
    architectural effect in vendor/airbender/00-master.md. This is a custom operation. -/
structure WriteInput where
  pc : Word
  before : Sail.State

/-- The project specifies an architectural no-op, followed by normal PC retirement.
    This does not specify witness-generation hints or application I/O. -/
abbrev writeSpec (input : WriteInput) (finalPC : Word) : Prop :=
  Sail.stepSpec input.before (pure SailRV32.Functions.RETIRE_SUCCESS)
    Sail.zeroRegister ⟨⟨0, 0⟩, finalPC⟩

def writeModel {p : Nat} [Fact p.Prime] :
    Verification.CircuitModel WriteInput Word (Nat → ZMod p) where
  satisfies := fun w => FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints
  represents := fun input finalPC w => PCMapping input.pc finalPC w ∧ w 7 = 0

/-- Decoder identifies the custom write and its zero-operand ADD preprocessing.
    Only PC bounds/reading are needed for the architectural no-op proof. -/
structure WriteInterfaces {p : Nat} [Fact p.Prime] (input : WriteInput)
    (_finalPC : Word) (w : Nat → ZMod p) : Prop where
  active : w 4 = 1
  selection : ∀ k, 10 ≤ k → k ≤ 18 → w k = if k = 10 then 1 else 0
  preprocessing : w 25 = 0 ∧ w 26 = 0 ∧ w 29 = 0 ∧ w 30 = 0 ∧ w 8 = 0 ∧ w 9 = 0
  initialPCBounds : input.pc.Bounded
  pcRead : Reference.Sail.run (SailRV32.Functions.get_arch_pc ()) input.before =
    .ok input.pc.toBitVec input.before

end Airbender.AddSub.NonDeterminism
