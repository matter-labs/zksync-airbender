import Airbender.Review.Trace.Families.ReducedMachine.SparseMainTheorems
import Airbender.Review.Circuits.ReducedMachine.DelegationSupport

namespace Airbender.Tests.NativeSparseMain
open Airbender.NativeSparseMain Airbender.NativeSparseMainProofs
open Airbender.ReducedMachine Airbender.ReducedMachine.Native
open Airbender.ReducedMachine.NativeMainAuxiliary Airbender.ReducedMachine.NativeMemoryBoundary
open Airbender.Blake2Worker Airbender.Blake2Worker.Native
abbrev TestF := ZMod mersenne31Modulus
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

theorem full_idle_body : FlatOperation.ConstraintsHoldFlat (Verification.environment NativeSparseMainProofs.idle)
    (importedConstraints NativeRuntimePool.table) := idle_body

theorem idle_no_request : NativeSparseMainProofs.idle 4 = 0 ∧ csrRequest NativeSparseMainProofs.idle = ⟨0,0,some 0,3⟩ := idle_fields

theorem csr1984_and_zero_oracle : NativeSparseMainProofs.idle 9 = 1984 ∧
    NativeSparseMainProofs.idle 90 = 0 ∧ NativeSparseMainProofs.idle 91 = 0 := by decide +kernel

theorem all_old_memory_tokens_retained (slot : Fin 3) (write : Bool) :
    mainMemoryKey NativeSparseMainProofs.idle slot write = mainMemoryKey original slot write := idle_memory slot write

theorem old_raw_alias_times : (mainMemoryKey NativeSparseMainProofs.idle 0 false).time = #v[0,0] ∧
    (mainMemoryKey NativeSparseMainProofs.idle 1 false).time = #v[4,0] ∧
    (mainMemoryKey NativeSparseMainProofs.idle 2 false).time = #v[5,0] := by decide +kernel

theorem both_pc_states_retained (write : Bool) : mainPCKey NativeSparseMainProofs.idle write = mainPCKey original write := idle_pc write

theorem all_init_fields_retained (write : Bool) : initializationKey NativeSparseMainProofs.idle write = initializationKey original write := idle_initialization write

theorem finite_spike_sum : (∑ i ∈ Finset.range 4, if i = 2 then (7 : TestF) else 0) = 7 := spike_sum 4 2 7 (by decide)

theorem selected_request (position : Fin (callerAuxiliaryLayout.traceLength-1)) : rows original position position.val 92 = 1 := by
  rw [row_request,if_pos rfl]

theorem other_request_zero (position : Fin (callerAuxiliaryLayout.traceLength-1)) (i : Nat) (different : i ≠ position.val) :
    rows original position i 92 = 0 := by rw [row_request,if_neg different]

theorem complete_domain_request_sum (position : Fin (callerAuxiliaryLayout.traceLength-1)) :
    (∑ i ∈ Finset.range (callerAuxiliaryLayout.traceLength-1), rows original position i 92) = (1 : TestF) := request_total position

theorem nonconstant_ordinary_rows (position : Fin (callerAuxiliaryLayout.traceLength-1)) :
    ∃ i < callerAuxiliaryLayout.traceLength-1, rows original position i ≠ rows original position position.val := nonconstant position

theorem selected_full_four_field_key (position : Fin (callerAuxiliaryLayout.traceLength-1)) :
    NativeDelegationSupport.callerKey (rows original position position.val) = ⟨1991,0,7,0⟩ := by
  simp only [rows]
  decide +kernel

theorem all_execute_zero (position : Fin (callerAuxiliaryLayout.traceLength-1)) (i : Nat) :
    rows original position i importedConstraintsTraceColumns.execute = 0 := all_inactive position i

theorem idle_caller_pole {R : Type} [Field R] (embed : TestF →+* R) :
    csrStageThreeArgument embed (⟨0,0,0,0⟩ : CSRArgumentChallenges R) 1 NativeSparseMainProofs.idle = 0 := by
  have kind : NativeSparseMainProofs.idle 94 = 0 := by decide +kernel
  simp [csrStageThreeArgument,kind]

theorem raw_padding_aux_zero {R : Type} [Field R] (embed : TestF →+* R) (memory : MemoryKeyChallenges R)
    (pc : PCChallenges R) (ch : CSRArgumentChallenges R) (position : Fin (callerAuxiliaryLayout.traceLength-1))
    (i : Nat) (different : i ≠ position.val) :
    (rawMemory embed memory pc ch position).auxiliary i callerAuxiliaryLayout.request = 0 := by
  rw [request_value,if_neg different]

theorem actual_reserved_value {R : Type} [Field R] (embed : TestF →+* R) (memory : MemoryKeyChallenges R)
    (pc : PCChallenges R) (ch : CSRArgumentChallenges R) (position : Fin (callerAuxiliaryLayout.traceLength-1)) :
    NativeCallerSumCompletion.normalizedAuxiliary (rawMemory embed memory pc ch position)
      (callerAuxiliaryLayout.traceLength-1) callerAuxiliaryLayout.request = -(csrStageThreeArgument embed ch 1 original)⁻¹ := by
  rw [NativeCallerSumCompletionProofs.terminal,request_sum]

theorem memory_columns_unchanged {R : Type} [Field R] (embed : TestF →+* R) (memory : MemoryKeyChallenges R)
    (pc : PCChallenges R) (ch : CSRArgumentChallenges R) (position : Fin (callerAuxiliaryLayout.traceLength-1))
    (i : Nat) (column : QuarticColumn) (other : column ≠ callerAuxiliaryLayout.request) :
    NativeCallerSumCompletion.normalizedAuxiliary (rawMemory embed memory pc ch position) i column =
      (rawMemory embed memory pc ch position).auxiliary i column :=
  NativeCallerSumCompletionProofs.other_column _ i column other
end Airbender.Tests.NativeSparseMain
