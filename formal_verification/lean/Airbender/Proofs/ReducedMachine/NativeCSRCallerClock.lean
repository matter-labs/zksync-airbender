import Airbender.Review.Helpers.Memory.ReducedMachineCSRCallers
import Airbender.Proofs.ReducedMachine.NativeTimestamp
import Airbender.Proofs.ReducedMachine.NativeRuntimeCSRResult
import Airbender.Proofs.Trace.History

namespace Airbender.ReducedMachine.NativeCSRCallerProofs
open Native Trace Verification
open Airbender.Trace.Proofs
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- Exact imported request fields and intermediate-state timestamp coordinates.
    The native stage-two caller uses this pair plus the imported offset. -/
theorem observation_columns (w : Nat → ZMod mersenne31Modulus) :
    csrCallerObservation (.mk .reduced w) =
      ⟨⟨w 92,w 94,some (w 93),3⟩,(w 2+3,w 3)⟩ := rfl

/-- Shared alignment/ranges make the actual caller clock canonical, strictly
    after all three native GPR accesses and before the next machine clock. -/
theorem clock {w : Nat → ZMod mersenne31Modulus}
    (inputs : ClockInputs importedConstraintsTraceColumns w)
    (effects : ClockEffects importedConstraintsTraceColumns w) :
    (timeOfPair (csrCallerObservation (.mk .reduced w)).time).Bounded ∧
      (csrCallerObservation (.mk .reduced w)).clock =
        (Row.mk .reduced w : Row mersenne31Modulus NativeReducedFamily).clock + 3 ∧
      (csrCallerObservation (.mk .reduced w)).clock % 4 = 3 ∧
      0 < (csrCallerObservation (.mk .reduced w)).clock ∧
      (csrCallerObservation (.mk .reduced w)).clock <
        (timeOfPair (Row.mk .reduced w : Row mersenne31Modulus NativeReducedFamily).finish.timestamp).value ∧
      ∀ port ∈ importedConstraintsMemoryPorts,
        (Row.mk .reduced w : Row mersenne31Modulus NativeReducedFamily).clock + port.clock.offset <
          (csrCallerObservation (.mk .reduced w)).clock := by
  have time := write_time (p := mersenne31Modulus) (by decide)
    (base := rawPair w importedConstraintsTraceColumns.initialTime) inputs.initial inputs.aligned
    (offset := 3) (by decide)
  have actual : (timeOfPair (csrCallerObservation (.mk .reduced w)).time).Bounded ∧
      (csrCallerObservation (.mk .reduced w)).clock =
        (Row.mk .reduced w : Row mersenne31Modulus NativeReducedFamily).clock+3 := by
    change (timeOfPair (w 2+3,w 3)).Bounded ∧
      (timeOfPair (w 2+3,w 3)).value = (timeOfPair (w 2,w 3)).value+3
    exact time
  have aligned := inputs.aligned
  change (w 2).val % 4 = 0 at aligned
  have rowAligned : (Row.mk .reduced w : Row mersenne31Modulus NativeReducedFamily).clock % 4 = 0 := by
    change ((w 2).val + 524288*(w 3).val)%4 = 0
    simp [Nat.add_mod,Nat.mul_mod,aligned]
  have advance := effects.advances
  change (timeOfPair (Row.mk .reduced w : Row mersenne31Modulus NativeReducedFamily).finish.timestamp).value =
    (Row.mk .reduced w : Row mersenne31Modulus NativeReducedFamily).clock+4 at advance
  refine ⟨actual.1,actual.2,by omega,by omega,by omega,?_⟩
  intro port member
  simp [importedConstraintsMemoryPorts] at member
  rcases member with rfl | rfl | rfl <;> dsimp <;> omega

/-- Actual selected multiplicity identifies the native runtime request kind and
    bounded ABI field. This is a local caller projection, not worker fulfillment. -/
theorem selected_request {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints NativeRuntimePool.table))
    (mask : w 12 = (csrMask : ZMod mersenne31Modulus))
    (selected : (csrRequest w).multiplicity = 1) :
    (csrCallerObservation (.mk .reduced w)).request.kind = 1991 ∧
      ∃ offset, (csrCallerObservation (.mk .reduced w)).request.offsetHigh = some offset ∧ offset.val < 65536 := by
  have effects := NativeRuntimeCSRResultProofs.effects holds mask
  have key : (w 9).val = 1991 := by
    rcases effects.key with nondeterminism | delegated
    · have multiplicity := congrArg CSRRequest.multiplicity effects.request
      have zero : (csrRequest w).multiplicity = 0 := by
        simpa [NativeRuntimeCSR.delegated,nondeterminism] using multiplicity
      exact False.elim (zero_ne_one (zero.symm.trans selected))
    · exact delegated
  have field : w 9 = 1991 := by
    calc
      w 9 = ((w 9).val : ZMod mersenne31Modulus) := by simp
      _ = 1991 := by rw [key]; norm_num
  have value1991 : (1991 : ZMod mersenne31Modulus).val = 1991 := by decide
  have kind := congrArg CSRRequest.kind effects.request
  have correct : (csrRequest w).kind = 1991 := by
    simpa [NativeRuntimeCSR.delegated,key,field,value1991] using kind
  exact ⟨correct,w 93,rfl,effects.offsetBounded⟩

end Airbender.ReducedMachine.NativeCSRCallerProofs
