import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Review.Helpers.Context.ExternalBoundary.BigintABI
import Airbender.Proofs.Bigint.Control

namespace Airbender.ExternalBoundary.BigintABI.Proofs
open Arithmetic
set_option warningAsError true
set_option maxHeartbeats 4000000
set_option maxRecDepth 32768

theorem input_word (w : Nat → ZMod p) : input w = ⟨(w 55).val, (w 56).val⟩ := by
  simp [input, Trace.readToken, Trace.MemoryPort.readCode,
    Bigint.importedConstraintsMemoryPorts, Trace.MemoryToken.word, Trace.pairCode]

theorem command_count (command : Command) : Bigint.Control.operationCount command.bits = 1 := by
  obtain ⟨opcode, carry⟩ := command
  fin_cases opcode <;> cases carry <;> decide

theorem command_nonzero (command : Command) : 0 < command.word.lo := by
  obtain ⟨opcode, carry⟩ := command
  fin_cases opcode <;> cases carry <;> decide

theorem mask_injective : Function.Injective Bigint.Control.mask := by
  intro a b equal
  have ba (i : Nat) (bound : i < 8) : a[i].toNat ≤ 1 := by cases a[i] <;> decide
  have bb (i : Nat) (bound : i < 8) : b[i].toNat ≤ 1 := by cases b[i] <;> decide
  have a0 := ba 0 (by decide); have a1 := ba 1 (by decide)
  have a2 := ba 2 (by decide); have a3 := ba 3 (by decide)
  have a4 := ba 4 (by decide); have a5 := ba 5 (by decide)
  have a6 := ba 6 (by decide); have a7 := ba 7 (by decide)
  have b0 := bb 0 (by decide); have b1 := bb 1 (by decide)
  have b2 := bb 2 (by decide); have b3 := bb 3 (by decide)
  have b4 := bb 4 (by decide); have b5 := bb 5 (by decide)
  have b6 := bb 6 (by decide); have b7 := bb 7 (by decide)
  norm_num [Bigint.Control.mask, Fin.sum_univ_succ] at equal
  have bits (i : Nat) (bound : i < 8) : a[i].toNat = b[i].toNat := by
    have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
    rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  apply Vector.ext
  intro i bound
  have same := bits i bound
  cases ha : a[i] <;> cases hb : b[i] <;> simp_all

theorem native_bits [Fact p.Prime] (hp : FieldCapacity.AtLeast p 256)
    {setup : Table (ZMod p) (fields 3)} {w : Nat → ZMod p}
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (Bigint.importedConstraints setup)) {command : Command} (binding : Binding w command) :
    Vector.ofFn (fun i : Fin 8 => (w Bigint.Variables.controlBits[i]).val == 1) = command.bits := by
  let output : Bigint.Control.Output := ⟨⟨(w 57).val, (w 58).val⟩,
    Vector.ofFn (fun i : Fin 8 => (w Bigint.Variables.controlBits[i]).val == 1)⟩
  have checked := Bigint.Control.Proofs.soundness hp setup (input w) output w
    ⟨holds, ⟨input_word w, rfl, rfl⟩⟩
  apply mask_injective
  exact checked.1.symm.trans (congrArg Word.lo binding)

theorem selected [Fact p.Prime] (hp : FieldCapacity.AtLeast p 256)
    {setup : Table (ZMod p) (fields 3)} {w : Nat → ZMod p}
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (Bigint.importedConstraints setup)) {command : Command} (binding : Binding w command) :
    w Bigint.Variables.operations[command.opcode] = 1 := by
  have bits := native_bits hp holds binding
  have selected := congrArg (fun b : Vector Bool 8 => b[command.bit]) bits
  have index : Bigint.Variables.controlBits[command.bit.val] = Bigint.Variables.operations[command.opcode.val] := by
    obtain ⟨opcode, carry⟩ := command
    fin_cases opcode <;> rfl
  simp only [Fin.getElem_fin, Vector.getElem_ofFn, index] at selected
  have good : command.bits[command.bit.val] = true := by simp [Command.bits]
  rw [good] at selected
  have value : (w Bigint.Variables.operations[command.opcode]).val = 1 := by simpa using selected
  have cast := congrArg (fun n : Nat => (n : ZMod p)) value
  simpa only [ZMod.natCast_zmod_val, Nat.cast_one] using cast

end Airbender.ExternalBoundary.BigintABI.Proofs
