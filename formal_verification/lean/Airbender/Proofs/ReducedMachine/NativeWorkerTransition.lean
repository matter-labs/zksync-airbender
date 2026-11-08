import Airbender.Review.Circuits.Blake2Worker.Transition
import Airbender.Proofs.ReducedMachine.NativeWorkerFinalization

namespace Airbender.NativeWorkerTransitionProofs
open Airbender.NativeWorkerTransition Airbender.Verification Airbender.Blake2Worker.Native
open Airbender.NativeWorkerFirstG (pack)
private abbrev F := ZMod mersenne31Modulus
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

private def columns {w : Nat → F} (e : Airbender.NativeWorkerFinalization.RowEffects w) :
    Airbender.NativeWorkerSecondCB.RowEffects w := e.prior.prior.prior.prior.prior.prior
private def routing {w : Nat → F} (e : Airbender.NativeWorkerFinalization.RowEffects w) :
    Airbender.NativeWorkerDiagonalFirst.RowEffects w := e.prior.prior.prior.prior.prior
private def addition {w : Nat → F} (e : Airbender.NativeWorkerFinalization.RowEffects w) :
    Airbender.NativeWorkerAddition.RowEffects w := (columns e).prior.prior.prior
private def initialized {w : Nat → F} (e : Airbender.NativeWorkerFinalization.RowEffects w) :
    Airbender.NativeWorkerInitial.RowEffects w := (addition e).prior.initial

/-- Exact control ABI is bound before any sampled values. -/
private theorem control_shape :
    (memoryAccess 42).readValue = #v[134,135] ∧
    (memoryAccess 42).writeValue = some #v[136,137] := by exact ⟨rfl,rfl⟩
private theorem state_shape (word : Fin 8) :
    (memoryAccess ⟨1+word.val,by have := word.isLt; omega⟩).readValue = #v[4+4*word.val,5+4*word.val] := by
  fin_cases word <;> rfl
private theorem extended_shape (word : Fin 16) :
    (memoryAccess ⟨9+word.val,by have := word.isLt; omega⟩).readValue = #v[36+4*word.val,37+4*word.val] := by
  fin_cases word <;> rfl
private theorem message_shape (word : Fin 16) :
    (memoryAccess ⟨26+word.val,by have := word.isLt; omega⟩).readValue = #v[102+2*word.val,103+2*word.val] := by
  fin_cases word <;> rfl

theorem read_state (w : Nat → F) (word : Fin 8) (limb : Fin 2) :
    (keyValue w ⟨1+word.val,by have := word.isLt; omega⟩ false)[limb] = (readInput w).state word limb := by
  fin_cases limb <;> simp [keyValue,state_shape,readInput,Airbender.NativeWorkerSchedule.state]
  exact congrArg w (by omega)
theorem read_extended (w : Nat → F) (word : Fin 16) (limb : Fin 2) :
    (keyValue w ⟨9+word.val,by have := word.isLt; omega⟩ false)[limb] = (readInput w).extended word limb := by
  fin_cases limb <;> simp [keyValue,extended_shape,readInput,Airbender.NativeWorkerInitial.oldExtended]
  exact congrArg w (by omega)
theorem read_message (w : Nat → F) (word : Fin 16) (limb : Fin 2) :
    (keyValue w ⟨26+word.val,by have := word.isLt; omega⟩ false)[limb] = (readInput w).message word limb := by
  fin_cases limb <;> simp [keyValue,message_shape,readInput,Airbender.NativeWorkerSchedule.message]
  exact congrArg w (by omega)
theorem read_control (w : Nat → F) :
    (keyValue w 42 false)[(0 : Fin 2)] = (readInput w).controlLow ∧
    (keyValue w 42 false)[(1 : Fin 2)].val = (readInput w).controlHigh := by
  simp [keyValue,control_shape.1,readInput]

theorem output_values (w : Nat → F) :
    observed w = ⟨Airbender.NativeWorkerFinalization.writeWord w,
      Airbender.NativeWorkerExtendedOutput.writeWord w,(w 136).val,(w 137).val⟩ := by
  have a : (fun word : Fin 8 => pack (keyValue w ⟨1+word.val,by have := word.isLt; omega⟩ true)[(0 : Fin 2)]
      (keyValue w ⟨1+word.val,by have := word.isLt; omega⟩ true)[(1 : Fin 2)]) =
      Airbender.NativeWorkerFinalization.writeWord w := by
    funext word
    rw [Airbender.NativeWorkerFinalizationProofs.write_value,Airbender.NativeWorkerFinalizationProofs.write_value]
    rfl
  have b : (fun word : Fin 16 => pack (keyValue w ⟨9+word.val,by have := word.isLt; omega⟩ true)[(0 : Fin 2)]
      (keyValue w ⟨9+word.val,by have := word.isLt; omega⟩ true)[(1 : Fin 2)]) =
      Airbender.NativeWorkerExtendedOutput.writeWord w := by
    funext word
    rw [Airbender.NativeWorkerExtendedOutputProofs.write_value,Airbender.NativeWorkerExtendedOutputProofs.write_value]
    rfl
  unfold observed
  rw [a,b]
  simp [keyValue,control_shape.2]

theorem input_values (w : Nat → F) :
    (readInput w).state = Airbender.NativeWorkerSchedule.state w ∧
    (readInput w).extended = Airbender.NativeWorkerInitial.oldExtended w ∧
    (readInput w).message = Airbender.NativeWorkerSchedule.message w ∧
    (readInput w).controlLow = w 134 ∧ (readInput w).controlHigh = (w 135).val := by
  exact ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem initial_word {w : Nat → F} (e : Airbender.NativeWorkerFinalization.RowEffects w) (word : Fin 16) :
    Airbender.NativeWorkerAddition.preGWord w word = initialWord (readInput w) word := by
  unfold Airbender.NativeWorkerAddition.preGWord
  rw [(initialized e).initialized word 0,(initialized e).initialized word 1]
  rfl

theorem selected_word {w : Nat → F} (e : Airbender.NativeWorkerFinalization.RowEffects w) (word : Fin 16) :
    Airbender.NativeWorkerAddition.messageWord w word = selectedWord (readInput w) word := by
  unfold Airbender.NativeWorkerAddition.messageWord
  rw [((addition e).selected word 0).1,((addition e).selected word 1).1]
  rfl

theorem column_result {w : Nat → F} (e : Airbender.NativeWorkerFinalization.RowEffects w) (c : Fin 4) :
    Airbender.NativeWorkerSecondCB.columnResult w c = column (readInput w) c := by
  rw [(columns e).complete]
  unfold column
  rw [initial_word e,initial_word e,initial_word e,initial_word e,selected_word e,selected_word e]

theorem routed_result {w : Nat → F} (e : Airbender.NativeWorkerFinalization.RowEffects w) (d c : Fin 4) :
    Airbender.NativeWorkerDiagonalFirst.inputWord w d c = routed (readInput w) d c := by
  rw [(routing e).routed,column_result e]
  rfl

theorem extended_result {w : Nat → F} (e : Airbender.NativeWorkerFinalization.RowEffects w) (word : Fin 16) :
    Airbender.NativeWorkerExtendedOutput.writeWord w word = extendedWord (readInput w) word := by
  rw [e.prior.result]
  unfold extendedWord diagonal
  rw [routed_result e,routed_result e,routed_result e,routed_result e,selected_word e,selected_word e]

theorem state_result {w : Nat → F} (e : Airbender.NativeWorkerFinalization.RowEffects w) (word : Fin 8) :
    Airbender.NativeWorkerFinalization.writeWord w word = stateWord (readInput w) word := by
  rw [e.finalized]
  unfold Airbender.NativeWorkerFinalization.xorResult stateWord
  rw [extended_result e,extended_result e]
  rfl

theorem control_result {w : Nat → F} (e : Airbender.NativeWorkerFinalization.RowEffects w) :
    (w 136).val = 0 ∧ (w 137).val = Airbender.NativeWorkerSchedule.nextHigh (w 135).val := by
  have h := (initialized e).schedule.update
  exact ⟨by rw [h.1]; rfl,h.2⟩

theorem result {w : Nat → F} (e : Airbender.NativeWorkerFinalization.RowEffects w) :
    observed w = transition (readInput w) := by
  rw [output_values]
  have state := funext (state_result e)
  have extended := funext (extended_result e)
  have control := control_result e
  exact congrArg₂ (fun a b => Output.mk a b (w 136).val (w 137).val) state extended |>.trans
    (by unfold transition; rw [control.1,control.2]; rfl)

theorem row {w : Nat → F} (e : Airbender.NativeWorkerFinalization.RowEffects w) : RowEffects w :=
  ⟨e,result e⟩

open Airbender.ReducedMachine.Native Airbender.Trace Airbender.ReducedMachine.NativeMemoryBoundary
theorem counted {Setup R : Type} [Field R]
    (publicSetup : SparseDecoderSetup Airbender.NativeCallerDecoder.Mode)
    (embed : F →+* R) (memory : MemoryKeyChallenges R) (ch : CSRArgumentChallenges R)
    (pc : PCChallenges R) (gamma : R)
    (decoder : Airbender.ReducedMachine.NativeDecoderArguments.Challenges R) (config : WorkerConfiguration Setup)
    {batch : Airbender.NativeMainDecoder.Batch R} {workers : WorkerBatch Setup R}
    {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : Airbender.NativeMainDecoder.SourceAccepted publicSetup embed memory ch pc gamma decoder config batch workers inputs inverse)
    {before : Reference.RiscV.Sail.State} {count : Nat}
    (image : Airbender.NativeCallerDecoder.setupImage before count 20 = some publicSetup)
    (lookups : Airbender.NativeMainDecoder.LogicalLookups publicSetup batch)
    (identity : Airbender.NativeDelegationSupport.SourceIdentity batch.main.proofs workers) :
    Airbender.NativeMixedReplay.Effects batch workers inputs ∧
      ∀ w ∈ Airbender.NativeTokenLedger.workerRows workers, RowEffects w := by
  have prior := Airbender.NativeWorkerFinalizationProofs.counted publicSetup embed memory ch pc gamma decoder config accepted image lookups identity
  exact ⟨prior.1,fun w member => row (prior.2 w member)⟩
end Airbender.NativeWorkerTransitionProofs
