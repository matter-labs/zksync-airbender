import Airbender.Proofs.ReducedMachine.NativeSparseMainBody
import Airbender.Proofs.ReducedMachine.NativeCallerSumCompletion

namespace Airbender.NativeSparseMainProofs
abbrev F := ZMod mersenne31Modulus
open Airbender.NativeSparseMain Airbender.NativeInactiveMain
open Airbender.ReducedMachine Airbender.ReducedMachine.Native
open Airbender.ReducedMachine.NativeMainAuxiliary Airbender.ReducedMachine.NativeMemoryBoundary
open Airbender.Blake2Worker Airbender.Blake2Worker.Native
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

theorem spike_sum {R : Type} [Field R] (n position : Nat) (value : R) (bound : position < n) :
    (∑ i ∈ Finset.range n, if i = position then value else 0) = value := by simp [bound]

theorem request_row {R : Type} [Field R] (embed : F →+* R) (memory : MemoryKeyChallenges R)
    (pc : PCChallenges R) {w : Nat → F} {aux : QuarticColumn → R} {next value : R}
    (old : RowAccepted embed memory pc w aux next) :
    RowAccepted embed memory pc w (withRequest value aux) next := by
  refine ⟨old.body,?_,?_,?_,old.padding,?_,?_⟩
  · intro slot
    have previous := old.memorySteps slot
    fin_cases slot <;> simpa [mainChainValue,withRequest,callerAuxiliaryLayout] using previous
  · simpa [mainChainValue,withRequest,callerAuxiliaryLayout] using old.state
  · simpa [withRequest,callerAuxiliaryLayout] using old.masking
  · simpa [withRequest,callerAuxiliaryLayout] using old.initialization
  · simpa [withRequest,callerAuxiliaryLayout] using old.grand

theorem idle_memory (slot : Fin 3) (write : Bool) : mainMemoryKey idle slot write = mainMemoryKey original slot write := by
  fin_cases slot <;> cases write <;> decide +kernel

theorem idle_pc (write : Bool) : mainPCKey idle write = mainPCKey original write := by
  cases write <;> decide +kernel

theorem idle_initialization (write : Bool) : initializationKey idle write = initializationKey original write := by
  cases write <;> decide +kernel

theorem idle_fields : idle 4 = 0 ∧ csrRequest idle = ⟨0,0,some 0,3⟩ := by decide +kernel

theorem original_padding : ∀ column ∈ initializationColumns, original column = 0 := by
  intro column member
  rw [NativeMainAuxiliaryProofs.initialization_geometry.2.2.2] at member
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at member
  rcases member with rfl|rfl|rfl|rfl|rfl|rfl <;> decide +kernel

theorem idle_padding : ∀ column ∈ initializationColumns, idle column = 0 := by
  intro column member
  rw [NativeMainAuxiliaryProofs.initialization_geometry.2.2.2] at member
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at member
  rcases member with rfl|rfl|rfl|rfl|rfl|rfl <;> decide +kernel

theorem original_row {R : Type} [Field R] (embed : F →+* R) (memory : MemoryKeyChallenges R)
    (pc : PCChallenges R) (ch : CSRArgumentChallenges R) (nonpoles : Nonpoles embed memory pc ch original) :
    RowAccepted embed memory pc original (NativeInactiveMainProofs.auxiliary embed memory pc ch original) 1 :=
  NativeInactiveMainProofs.row embed memory pc ch (NativeCSRPositiveWitness.body false) (by rfl) original_padding nonpoles

theorem idle_row {R : Type} [Field R] (embed : F →+* R) (memory : MemoryKeyChallenges R)
    (pc : PCChallenges R) (ch : CSRArgumentChallenges R) (nonpoles : Nonpoles embed memory pc ch original) :
    RowAccepted embed memory pc idle (NativeInactiveMainProofs.auxiliary embed memory pc ch original) 1 := by
  have old := original_row embed memory pc ch nonpoles
  refine ⟨idle_body,?_,?_,?_,?_,?_,old.grand⟩
  · intro slot
    simpa only [idle_memory] using old.memorySteps slot
  · simpa only [idle_pc] using old.state
  · simpa only [show idle importedConstraintsTraceColumns.execute = original importedConstraintsTraceColumns.execute by decide +kernel] using old.masking
  · intro column member
    rw [idle_padding column member]
    simp [processingMaskTerm]
  · simpa only [idle_initialization] using old.initialization

noncomputable def rawAuxiliary {R : Type} [Field R] (embed : F →+* R) (memory : MemoryKeyChallenges R)
    (pc : PCChallenges R) (ch : CSRArgumentChallenges R)
    (position : Fin (callerAuxiliaryLayout.traceLength-1)) (i : Nat) : QuarticColumn → R :=
  withRequest (if i = position.val then (csrStageThreeArgument embed ch 1 original)⁻¹ else 0)
    (NativeInactiveMainProofs.auxiliary embed memory pc ch original)

noncomputable def rawMemory {R : Type} [Field R] (embed : F →+* R) (memory : MemoryKeyChallenges R)
    (pc : PCChallenges R) (ch : CSRArgumentChallenges R)
    (position : Fin (callerAuxiliaryLayout.traceLength-1)) : MainProof R :=
  ⟨rows original position,rawAuxiliary embed memory pc ch position,1⟩

theorem raw_memory {R : Type} [Field R] (embed : F →+* R) (memory : MemoryKeyChallenges R)
    (pc : PCChallenges R) (ch : CSRArgumentChallenges R)
    (position : Fin (callerAuxiliaryLayout.traceLength-1)) (nonpoles : Nonpoles embed memory pc ch original) :
    Accepted embed memory pc (rawMemory embed memory pc ch position) := by
  constructor
  · intro i _
    have grand : rawAuxiliary embed memory pc ch position (i+1) callerAuxiliaryLayout.grandProduct = 1 := by
      simp [rawAuxiliary,withRequest,NativeInactiveMainProofs.auxiliary,callerAuxiliaryLayout]
    change RowAccepted embed memory pc (rows original position i) (rawAuxiliary embed memory pc ch position i)
      (rawAuxiliary embed memory pc ch position (i+1) callerAuxiliaryLayout.grandProduct)
    rw [grand]
    by_cases same : i = position.val
    · simpa [rows,rawAuxiliary,same] using request_row embed memory pc (original_row embed memory pc ch nonpoles)
    · simpa [rows,rawAuxiliary,same] using request_row embed memory pc (idle_row embed memory pc ch nonpoles)
  · simp [rawMemory,rawAuxiliary,withRequest,NativeInactiveMainProofs.auxiliary,callerAuxiliaryLayout,grandBoundaryTerm]
  · simp [rawMemory,rawAuxiliary,withRequest,NativeInactiveMainProofs.auxiliary,callerAuxiliaryLayout,grandBoundaryTerm]

theorem raw_caller {R : Type} [Field R] (embed : F →+* R) (memory : MemoryKeyChallenges R)
    (pc : PCChallenges R) (ch : CSRArgumentChallenges R)
    (position : Fin (callerAuxiliaryLayout.traceLength-1)) (nonpoles : Nonpoles embed memory pc ch original) (i : Nat) :
    callerAuxiliaryTerm 1 (csrStageThreeArgument embed ch 1 ((rawMemory embed memory pc ch position).rows i))
      (embed (csrRequest ((rawMemory embed memory pc ch position).rows i)).multiplicity)
      ((rawMemory embed memory pc ch position).auxiliary i callerAuxiliaryLayout.request) = 0 := by
  have request := congrArg CSRRequest.multiplicity (NativeCSRBodyPaddingProofs.observations false).2
  by_cases same : i = position.val
  · simp [rawMemory,rows,rawAuxiliary,withRequest,same,callerAuxiliaryTerm,request,mul_inv_cancel₀ nonpoles.2.2]
  · simp [rawMemory,rows,rawAuxiliary,withRequest,same,callerAuxiliaryTerm,idle_fields.2]

theorem raw_decoder {R : Type} [Field R] (embed : F →+* R) (memory : MemoryKeyChallenges R)
    (pc : PCChallenges R) (ch : CSRArgumentChallenges R)
    (decoder : NativeDecoderArguments.Challenges R) (position : Fin (callerAuxiliaryLayout.traceLength-1)) (i : Nat) :
    NativeDecoderArguments.RowAccepted embed decoder ((rawMemory embed memory pc ch position).rows i)
      ((rawMemory embed memory pc ch position).auxiliary i) := by
  constructor
  · by_cases same : i = position.val
    · simpa [rawMemory,rows,same] using NativeCSRPositiveWitness.body false
    · simpa [rawMemory,rows,same] using idle_body
  · by_cases same : i = position.val <;>
      simp [rawMemory,rows,rawAuxiliary,withRequest,same,NativeDecoderArguments.accessTerm,
        NativeInactiveMainProofs.auxiliary,callerAuxiliaryLayout,decoderAuxiliaryLayout,
        importedConstraintsTraceColumns,idle_fields.1,show original 4 = 0 by rfl]

theorem request_value {R : Type} [Field R] (embed : F →+* R) (memory : MemoryKeyChallenges R)
    (pc : PCChallenges R) (ch : CSRArgumentChallenges R)
    (position : Fin (callerAuxiliaryLayout.traceLength-1)) (i : Nat) :
    (rawMemory embed memory pc ch position).auxiliary i callerAuxiliaryLayout.request =
      if i = position.val then (csrStageThreeArgument embed ch 1 original)⁻¹ else 0 := by
  simp [rawMemory,rawAuxiliary,withRequest]

theorem request_sum {R : Type} [Field R] (embed : F →+* R) (memory : MemoryKeyChallenges R)
    (pc : PCChallenges R) (ch : CSRArgumentChallenges R) (position : Fin (callerAuxiliaryLayout.traceLength-1)) :
    NativeCallerSumCompletion.requestSum (rawMemory embed memory pc ch position) =
      (csrStageThreeArgument embed ch 1 original)⁻¹ := by
  unfold NativeCallerSumCompletion.requestSum
  simp only [request_value]
  exact spike_sum _ _ _ position.isLt

theorem row_request (position : Fin (callerAuxiliaryLayout.traceLength-1)) (i : Nat) :
    rows original position i 92 = if i = position.val then 1 else 0 := by
  have yes := congrArg CSRRequest.multiplicity (NativeCSRBodyPaddingProofs.observations false).2
  have no := congrArg CSRRequest.multiplicity idle_fields.2
  change original 92 = 1 at yes
  change idle 92 = 0 at no
  by_cases same : i = position.val <;> simp [rows,same,yes,no]

theorem request_total (position : Fin (callerAuxiliaryLayout.traceLength-1)) :
    (∑ i ∈ Finset.range (callerAuxiliaryLayout.traceLength-1), rows original position i 92) = (1 : F) := by
  simp only [row_request]
  exact spike_sum _ _ _ position.isLt

theorem all_inactive (position : Fin (callerAuxiliaryLayout.traceLength-1)) (i : Nat) :
    rows original position i importedConstraintsTraceColumns.execute = 0 := by
  by_cases same : i = position.val <;> simp [rows,same,importedConstraintsTraceColumns,idle_fields.1,show original 4 = 0 by rfl]

theorem nonconstant (position : Fin (callerAuxiliaryLayout.traceLength-1)) :
    ∃ i < callerAuxiliaryLayout.traceLength-1, rows original position i ≠ rows original position position.val := by
  let i := if position.val = 0 then 1 else 0
  have small : i < callerAuxiliaryLayout.traceLength-1 := by
    change i < 8388607
    simp only [i]; split_ifs <;> omega
  have different : i ≠ position.val := by simp only [i]; split_ifs <;> omega
  refine ⟨i,small,?_⟩
  intro same
  have values := congrArg (fun w : Nat → F => w 92) same
  rw [row_request,row_request,if_neg different,if_pos rfl] at values
  exact zero_ne_one values

/-- Entire normalized polynomial and component assembly BEFORE native sampling. -/
theorem complete_components {R : Type} [Field R] (embed : F →+* R) (memory : MemoryKeyChallenges R)
    (pc : PCChallenges R) (ch : CSRArgumentChallenges R) (decoder : NativeDecoderArguments.Challenges R)
    (base : MainProof R) (old : Accepted embed memory pc base)
    (callers : ∀ i < callerAuxiliaryLayout.traceLength-1,
      callerAuxiliaryTerm 1 (csrStageThreeArgument embed ch 1 (base.rows i))
        (embed (csrRequest (base.rows i)).multiplicity) (base.auxiliary i callerAuxiliaryLayout.request) = 0)
    (decoders : ∀ i < callerAuxiliaryLayout.traceLength-1, NativeDecoderArguments.RowAccepted embed decoder (base.rows i) (base.auxiliary i))
    (omega : R) (primitive : IsPrimitiveRoot omega callerAuxiliaryLayout.traceLength) :
    ∃ main : NativeMainArguments.Proof R,
      main.memory.rows = base.rows ∧ main.memory.grandClaim = base.grandClaim ∧
      Accepted embed memory pc main.memory ∧ CallerDelegationAccepted embed ch main.caller ∧
      (∀ i < callerAuxiliaryLayout.traceLength-1, NativeDecoderArguments.RowAccepted embed decoder (main.memory.rows i) (main.memory.auxiliary i)) ∧
      main.delegationClaim = NativeCallerSumCompletion.requestSum base := by
  obtain ⟨polynomial,samples⟩ := Delegation.SumCompletionProofs.normalized_completion
    (by decide : 0 < callerAuxiliaryLayout.traceLength) primitive (NativeCallerSumCompletionProofs.domain_nonzero embed)
    (fun i => base.auxiliary i callerAuxiliaryLayout.request)
  let main : NativeMainArguments.Proof R :=
    ⟨NativeCallerSumCompletion.normalizedMemory base,polynomial,omega,NativeCallerSumCompletion.requestSum base⟩
  have memoryAccepted : Accepted embed memory pc main.memory := by
    constructor
    · intro i small
      change RowAccepted embed memory pc (base.rows i) (NativeCallerSumCompletion.normalizedAuxiliary base i)
        (NativeCallerSumCompletion.normalizedAuxiliary base (i+1) callerAuxiliaryLayout.grandProduct)
      rw [NativeCallerSumCompletionProofs.ordinary base small,NativeCallerSumCompletionProofs.grand]
      exact old.rows i small
    · change grandBoundaryTerm 1 (NativeCallerSumCompletion.normalizedAuxiliary base 0 callerAuxiliaryLayout.grandProduct) 1 = 0
      rw [NativeCallerSumCompletionProofs.grand]
      exact old.first
    · change grandBoundaryTerm 1 (NativeCallerSumCompletion.normalizedAuxiliary base (callerAuxiliaryLayout.traceLength-1) callerAuxiliaryLayout.grandProduct) base.grandClaim = 0
      rw [NativeCallerSumCompletionProofs.grand]
      exact old.last
  have caller : CallerDelegationAccepted embed ch
      ⟨base.rows,NativeCallerSumCompletion.normalizedAuxiliary base,polynomial,omega,NativeCallerSumCompletion.requestSum base⟩ := by
    refine ⟨fun i small => (memoryAccepted.rows i small).body,?_,?_⟩
    · intro i small
      change callerAuxiliaryTerm 1 (csrStageThreeArgument embed ch 1 (base.rows i))
        (embed (csrRequest (base.rows i)).multiplicity) (NativeCallerSumCompletion.normalizedAuxiliary base i callerAuxiliaryLayout.request) = 0
      rw [NativeCallerSumCompletionProofs.ordinary base small]
      exact callers i small
    · simpa only [NativeCallerSumCompletionProofs.request_column,NativeCallerSumCompletion.requestSum] using samples
  have view : main.caller =
      ⟨base.rows,NativeCallerSumCompletion.normalizedAuxiliary base,polynomial,omega,NativeCallerSumCompletion.requestSum base⟩ := by
    simp only [main,NativeMainArguments.Proof.caller,NativeCallerSumCompletion.normalizedMemory]
  refine ⟨main,?_,?_,memoryAccepted,?_,?_,?_⟩
  · simp only [main,NativeCallerSumCompletion.normalizedMemory]
  · simp only [main,NativeCallerSumCompletion.normalizedMemory]
  · rw [view]; exact caller
  · intro i small
    change NativeDecoderArguments.RowAccepted embed decoder (base.rows i) (NativeCallerSumCompletion.normalizedAuxiliary base i)
    rw [NativeCallerSumCompletionProofs.ordinary base small]
    exact decoders i small
  · simp only [main]

/-- Genuine original caller sum polynomial for this nonconstant FULL ordinary
    memory component. The reserved caller value is its actual negative ordinary
    sum; all other columns/rows are retained. No global source/worker claim. -/
theorem complete {R : Type} [Field R] (embed : F →+* R) (memory : MemoryKeyChallenges R)
    (pc : PCChallenges R) (ch : CSRArgumentChallenges R) (decoder : NativeDecoderArguments.Challenges R)
    (position : Fin (callerAuxiliaryLayout.traceLength-1)) (nonpoles : Nonpoles embed memory pc ch original)
    (omega : R) (primitive : IsPrimitiveRoot omega callerAuxiliaryLayout.traceLength) :
    ∃ main : NativeMainArguments.Proof R,
      main.memory.rows = rows original position ∧ main.memory.grandClaim = 1 ∧
      Accepted embed memory pc main.memory ∧ CallerDelegationAccepted embed ch main.caller ∧
      (∀ i < callerAuxiliaryLayout.traceLength-1, NativeDecoderArguments.RowAccepted embed decoder (main.memory.rows i) (main.memory.auxiliary i)) ∧
      main.delegationClaim = (csrStageThreeArgument embed ch 1 original)⁻¹ ∧ main.delegationClaim ≠ 0 := by
  obtain ⟨main,rowsSame,grand,memoryAccepted,caller,decoders,claim⟩ := complete_components embed memory pc ch decoder
    (rawMemory embed memory pc ch position) (raw_memory embed memory pc ch position nonpoles)
    (fun i _ => raw_caller embed memory pc ch position nonpoles i)
    (fun i _ => raw_decoder embed memory pc ch decoder position i) omega primitive
  have actual : main.delegationClaim = (csrStageThreeArgument embed ch 1 original)⁻¹ :=
    claim.trans (request_sum embed memory pc ch position)
  refine ⟨main,rowsSame,grand,memoryAccepted,caller,decoders,actual,?_⟩
  rw [actual]
  exact inv_ne_zero nonpoles.2.2

end Airbender.NativeSparseMainProofs
