import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Review.Circuits.Bigint.Call
import Airbender.Proofs.ExternalBoundary.BigintABI

namespace Airbender.Bigint.Call.Proofs
open Arithmetic
open Trace Reference.RiscV.Sail
set_option warningAsError true
set_option maxRecDepth 32768
set_option maxHeartbeats 2400000

theorem operation {w : Nat → ZMod p} {command : ExternalBoundary.BigintABI.Command}
    (effects : Native.ArithmeticEffects w)
    (selected : w Variables.operations[command.opcode] = 1)
    (carry : ((w 65).val == 1) = command.carry) :
    Operation command (Native.limbs w Variables.leftLimbs)
      (Native.limbs w Variables.rightLimbs) (Native.output w) := by
  obtain ⟨opcode, incoming⟩ := command
  fin_cases opcode
  · simpa [Operation, Native.additiveInput, carry] using effects.1 .add selected
  · simpa [Operation, Native.additiveInput, carry] using effects.1 .sub selected
  · simpa [Operation, Native.additiveInput, carry] using effects.1 .reverseSub selected
  · exact effects.2.2 .low selected
  · exact effects.2.2 .high selected
  · exact effects.2.1 selected
  · simpa [Operation, Native.additiveInput, carry] using effects.1 .copy selected

theorem incoming_carry [Fact p.Prime] (hp : FieldCapacity.AtLeast p 256)
    {setup : Table (ZMod p) (fields 3)} {w : Nat → ZMod p}
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints setup)) {command : ExternalBoundary.BigintABI.Command}
    (binding : ExternalBoundary.BigintABI.Binding w command) :
    ((w 65).val == 1) = command.carry := by
  have bits := ExternalBoundary.BigintABI.Proofs.native_bits hp holds binding
  have same := congrArg (fun b : Vector Bool 8 => b[6]) bits
  have notCarry : command.bit ≠ 6 := by
    obtain ⟨opcode, carry⟩ := command
    fin_cases opcode <;> simp [ExternalBoundary.BigintABI.Command.bit, Fin.ext_iff]
  simpa [Variables.controlBits, ExternalBoundary.BigintABI.Command.bits,
    Ne.symm notCarry] using same

theorem executes_of_footprint {pointers : Addresses.Input}
    {command : ExternalBoundary.BigintABI.Command} {left right : Vector Nat 16}
    {output : Bigint.Output} {before after : State}
    (abi : Addresses.PointerABI pointers)
    (bounds : (∀ i : Fin 16, left[i] < limbBase) ∧ (∀ i : Fin 16, right[i] < limbBase))
    (reads : ∀ i : Fin 19, (cells pointers)[i].read before =
      .ok (operands pointers command left right)[i] before)
    (effect : Operation command left right output)
    (written : AtomicWrites (writes pointers right output) before after) : Executes before after := by
  have registers (i : Fin 19) := reads i
  have r10 := registers 0
  have r11 := registers 9
  have r12 := registers 18
  simp only [cells, operands, results, Fin.getElem_fin, Vector.getElem_ofFn] at r10 r11 r12
  refine ⟨pointers, command, left, right, output, abi, r10, r11, r12,
    ⟨bounds.1, ?_⟩, ⟨bounds.2, ?_⟩, effect, written⟩
  · intro i
    have actual := reads ⟨i.val + 1, by omega⟩
    fin_cases i <;> simpa [cells, operands, results, Fin.getElem_fin] using actual
  · intro i
    have actual := reads ⟨i.val + 10, by omega⟩
    fin_cases i <;> simpa [cells, operands, results, Fin.getElem_fin] using actual

theorem command_control_range (command : ExternalBoundary.BigintABI.Command) :
    0 < command.word.toBitVec.toNat ∧ command.word.toBitVec.toNat < 256 := by
  obtain ⟨opcode, carry⟩ := command
  fin_cases opcode <;> cases carry <;> decide

theorem executes_control_range {before after : State} (execution : Executes before after) :
    ∃ control : BitVec 32, (Cell.register 12).read before = .ok control before ∧
      0 < control.toNat ∧ control.toNat < 256 := by
  obtain ⟨_, command, _, _, _, _, _, _, read, _⟩ := execution
  exact ⟨command.word.toBitVec, read, command_control_range command⟩

end Airbender.Bigint.Call.Proofs
