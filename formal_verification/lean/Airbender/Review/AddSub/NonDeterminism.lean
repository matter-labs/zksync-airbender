import Airbender.Review.AddSub.Artifact
import Airbender.Review.AddSub.Reference
import Airbender.Review.Properties

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

/-- An external stream and read position are reference inputs, supplied
    independently of the circuit witness. This custom operation is the pinned
    project's CSRRW rd,0x7C0,x0, not the standard Sail CSR implementation. -/
structure ReadInput where
  stream : List (BitVec 32)
  position : Nat
  rd : SailRV32.regidx
  pc : Word
  before : Sail.State

/-- One selected external response, using Sail's native register/PC effects.
    Whole-trace consumption/order is a separate claim. -/
def readSpec (input : ReadInput) (output : Sail.Output) : Prop :=
  ∃ response, input.stream[input.position]? = some response ∧
    output.destination.Bounded ∧
    Sail.stepSpec input.before
      (do SailRV32.Functions.wX_bits input.rd response
          pure SailRV32.Functions.RETIRE_SUCCESS) input.rd output

/-- Observable columns and the explicit external response-port interpretation.
    The circuit leaves these response limbs free. This mapping does NOT prove
    that Airbender binds an independently fixed stream; it states the external
    input connection required for that stronger claim. The stream is never
    constructed from output witnesses. -/
structure ReadMapping {p : Nat} (input : ReadInput) (output : Sail.Output)
    (w : Nat → ZMod p) : Prop where
  pc : PCMapping input.pc output.pc w
  destinationIndex : match input.rd with
    | .Regidx bits => w 7 = (bits.toNat : ZMod p)
  outputLo : output.destination.lo = (w 33).val
  outputHi : output.destination.hi = (w 34).val
  responsePort : ∃ response, input.stream[input.position]? = some response ∧
    w 33 = ((Word.ofBitVec response).lo : ZMod p) ∧
    w 34 = ((Word.ofBitVec response).hi : ZMod p)

def readModel {p : Nat} [Fact p.Prime] :
    Verification.CircuitModel ReadInput Sail.Output (Nat → ZMod p) where
  satisfies := fun w => FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints
  represents := ReadMapping

structure ReadInterfaces {p : Nat} [Fact p.Prime] (input : ReadInput)
    (_output : Sail.Output) (w : Nat → ZMod p) : Prop where
  active : w 4 = 1
  nonzeroDestination : input.rd ≠ Sail.zeroRegister
  selection : ∀ k, 10 ≤ k → k ≤ 18 → w k = if k = 18 then 1 else 0
  initialPCBounds : input.pc.Bounded
  pcRead : Reference.Sail.run (SailRV32.Functions.get_arch_pc ()) input.before =
    .ok input.pc.toBitVec input.before

end Airbender.AddSub.NonDeterminism
