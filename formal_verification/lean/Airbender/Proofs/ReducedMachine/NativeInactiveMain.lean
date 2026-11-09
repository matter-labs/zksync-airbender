import Airbender.Proofs.ReducedMachine.NativeCSRBodyPadding
import Airbender.Proofs.ReducedMachine.NativeMainAuxiliary
import Airbender.Proofs.ReducedMachine.NativeCallerDelegation
import Airbender.Review.Trace.Families.ReducedMachine.InactiveMain

namespace Airbender.NativeInactiveMainProofs
open Airbender.NativeInactiveMain Airbender.ReducedMachine Airbender.ReducedMachine.Native
open Airbender.ReducedMachine.NativeMainAuxiliary Airbender.ReducedMachine.NativeMemoryBoundary
open Airbender.Blake2Worker Airbender.Blake2Worker.Native
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

/-- Generic cumulative chain before actual native witness sampling. -/
def chain {R : Type} [Field R] (read write : Nat → R) : Nat → R
  | 0 => 1
  | n+1 => chain read write n * write n / read n

theorem chain_step {R : Type} [Field R] (read write : Nat → R) (n : Nat) (nonzero : read n ≠ 0) :
    chain read write (n+1) * read n = chain read write n * write n := by
  simp only [chain,div_mul_cancel₀ _ nonzero]

def factor {R : Type} [Field R] (embed : F →+* R) (memory : MemoryKeyChallenges R)
    (w : Nat → F) (write : Bool) (n : Nat) : R :=
  memoryKeyArgument embed memory (mainMemoryKey w ⟨n%3,Nat.mod_lt _ (by decide)⟩ write)

noncomputable def auxiliary {R : Type} [Field R] (embed : F →+* R) (memory : MemoryKeyChallenges R)
    (pc : PCChallenges R) (ch : CSRArgumentChallenges R) (w : Nat → F) (column : QuarticColumn) : R :=
  if column.start = 96 then chain (factor embed memory w false) (factor embed memory w true) 1
  else if column.start = 100 then chain (factor embed memory w false) (factor embed memory w true) 2
  else if column.start = 104 then chain (factor embed memory w false) (factor embed memory w true) 3
  else if column.start = 108 then chain (factor embed memory w false) (factor embed memory w true) 3 *
    pcArgument embed pc (mainPCKey w true) / pcArgument embed pc (mainPCKey w false)
  else if column.start = 112 ∨ column.start = 116 ∨ column.start = 120 then 1
  else if column.start = 92 then (csrStageThreeArgument embed ch 1 w)⁻¹ else 0

theorem chain_columns {R : Type} [Field R] (embed : F →+* R) (memory : MemoryKeyChallenges R)
    (pc : PCChallenges R) (ch : CSRArgumentChallenges R) (w : Nat → F) (slot : Fin 3) :
    mainChainValue (auxiliary embed memory pc ch w) slot.val =
      chain (factor embed memory w false) (factor embed memory w true) slot.val ∧
    auxiliary embed memory pc ch w callerAuxiliaryLayout.memory[slot.val]! =
      chain (factor embed memory w false) (factor embed memory w true) (slot.val+1) := by
  fin_cases slot <;> simp [mainChainValue,auxiliary,chain,callerAuxiliaryLayout]

theorem row {R : Type} [Field R] (embed : F →+* R) (memory : MemoryKeyChallenges R)
    (pc : PCChallenges R) (ch : CSRArgumentChallenges R) {w : Nat → F}
    (body : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints NativeRuntimePool.table))
    (inactive : w 4 = 0) (padding : ∀ column ∈ initializationColumns, w column = 0)
    (nonpoles : Nonpoles embed memory pc ch w) :
    RowAccepted embed memory pc w (auxiliary embed memory pc ch w) 1 := by
  constructor
  · exact body
  · intro slot
    rw [(chain_columns embed memory pc ch w slot).1,(chain_columns embed memory pc ch w slot).2]
    have step := chain_step (factor embed memory w false) (factor embed memory w true) slot.val
      (by simpa only [factor,Nat.mod_eq_of_lt slot.isLt] using nonpoles.1 slot)
    simpa only [memoryAuxiliaryTerm,one_mul,sub_eq_zero,factor,Nat.mod_eq_of_lt slot.isLt] using step
  · have step := div_mul_cancel₀
      (chain (factor embed memory w false) (factor embed memory w true) 3 * pcArgument embed pc (mainPCKey w true)) nonpoles.2.1
    simpa [mainChainValue,auxiliary,callerAuxiliaryLayout,memoryAuxiliaryTerm] using sub_eq_zero.mpr step
  · simp [permutationMaskTerm,auxiliary,callerAuxiliaryLayout,importedConstraintsTraceColumns,inactive]
  · intro column member
    rw [padding column member]
    simp [processingMaskTerm]
  · have zeros : w 126 = 0 ∧ w 127 = 0 ∧ w 128 = 0 ∧ w 129 = 0 ∧ w 130 = 0 ∧ w 131 = 0 := by
      simpa only [NativeMainAuxiliaryProofs.initialization_geometry.2.2.2,List.mem_cons,List.mem_nil_iff,or_false,forall_eq_or_imp,forall_eq] using padding
    have same : initializationKey w false = initializationKey w true := by
      simp [initializationKey,importedConstraintsArgumentColumns,zeros.2.2.1,zeros.2.2.2.1,zeros.2.2.2.2.1,zeros.2.2.2.2.2]
    simp [memoryAuxiliaryTerm,auxiliary,callerAuxiliaryLayout,same]
  · simp [grandProductTerm,auxiliary,callerAuxiliaryLayout]

noncomputable def proof {R : Type} [Field R] (embed : F →+* R) (memory : MemoryKeyChallenges R)
    (pc : PCChallenges R) (ch : CSRArgumentChallenges R) (w : Nat → F) : MainProof R :=
  ⟨fun _ => w,fun _ => auxiliary embed memory pc ch w,1⟩

theorem realizes {R : Type} [Field R] (embed : F →+* R) (memory : MemoryKeyChallenges R)
    (pc : PCChallenges R) (ch : CSRArgumentChallenges R)
    (decoder : Airbender.ReducedMachine.NativeDecoderArguments.Challenges R) {w : Nat → F}
    (body : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints NativeRuntimePool.table))
    (inactive : w 4 = 0) (padding : ∀ column ∈ initializationColumns, w column = 0)
    (request : (csrRequest w).multiplicity = 1) (nonpoles : Nonpoles embed memory pc ch w) :
    Realizes embed memory pc ch decoder w (proof embed memory pc ch w) := by
  refine ⟨rfl,rfl,⟨fun _ _ => ?_,?_,?_⟩,fun _ _ => ?_,fun _ _ => ?_⟩
  · exact row embed memory pc ch body inactive padding nonpoles
  · simp [proof,auxiliary,callerAuxiliaryLayout,grandBoundaryTerm]
  · simp [proof,auxiliary,callerAuxiliaryLayout,grandBoundaryTerm]
  · have actual : auxiliary embed memory pc ch w callerAuxiliaryLayout.request = (csrStageThreeArgument embed ch 1 w)⁻¹ := by
      simp [auxiliary,callerAuxiliaryLayout]
    change callerAuxiliaryTerm 1 (csrStageThreeArgument embed ch 1 w) (embed (csrRequest w).multiplicity)
      (auxiliary embed memory pc ch w callerAuxiliaryLayout.request) = 0
    rw [request,map_one,actual]
    simp only [callerAuxiliaryTerm,one_mul,mul_inv_cancel₀ nonpoles.2.2,sub_self]
  · refine ⟨body,?_⟩
    simp [proof,Airbender.ReducedMachine.NativeDecoderArguments.accessTerm,auxiliary,decoderAuxiliaryLayout,importedConstraintsTraceColumns,inactive]

theorem fixture : ∃ w, Fixture w := by
  refine ⟨NativeCSRPositiveWitness.assignment false,?_,?_,?_⟩
  · exact (NativeCSRBodyPaddingProofs.observations false).1
  · exact (NativeCSRBodyPaddingProofs.observations false).2
  · intro R _ embed memory pc ch decoder nonpoles
    refine ⟨proof embed memory pc ch _,realizes embed memory pc ch decoder (NativeCSRPositiveWitness.body false) ?_ ?_ ?_ nonpoles⟩
    · rfl
    · intro column member
      have slots : initializationColumns = [126,127,128,129,130,131] := NativeMainAuxiliaryProofs.initialization_geometry.2.2.2
      rw [slots] at member
      simp only [List.mem_cons,List.mem_nil_iff,or_false] at member
      rcases member with rfl|rfl|rfl|rfl|rfl|rfl <;> decide +kernel
    · exact congrArg CSRRequest.multiplicity (NativeCSRBodyPaddingProofs.observations false).2

/-- Explicit nonempty challenge domain for the fixture, not a sampled transcript. -/
def sampleMemory {R : Type} [Field R] : MemoryKeyChallenges R := ⟨0,0,0,0,0,0,0⟩
def samplePC {R : Type} [Field R] : PCChallenges R := ⟨1,0,0,0⟩
def sampleCaller {R : Type} [Field R] (embed : F →+* R) : CSRArgumentChallenges R :=
  ⟨1-embed 1991,0,0,0⟩

theorem fixture_registers (slot : Fin 3) :
    (mainMemoryKey (NativeCSRPositiveWitness.assignment false) slot false).address.isRegister = 1 := by
  fin_cases slot <;> decide +kernel

theorem sample_nonpoles {R : Type} [Field R] (embed : F →+* R) :
    Nonpoles embed sampleMemory samplePC (sampleCaller embed) (NativeCSRPositiveWitness.assignment false) := by
  have pcLow : (mainPCKey (NativeCSRPositiveWitness.assignment false) false).pc[0] = 0 := by decide +kernel
  have kind : NativeCSRPositiveWitness.assignment false 94 = (1991 : F) := by decide +kernel
  refine ⟨?_,?_,?_⟩
  · intro slot
    simp [memoryKeyArgument,sampleMemory,fixture_registers]
  · simp [pcArgument,samplePC,pcLow]
  · simp [csrStageThreeArgument,sampleCaller,kind]

theorem sample_realizes {R : Type} [Field R] (embed : F →+* R)
    (decoder : Airbender.ReducedMachine.NativeDecoderArguments.Challenges R) :
    Realizes embed sampleMemory samplePC (sampleCaller embed) decoder (NativeCSRPositiveWitness.assignment false)
      (proof embed sampleMemory samplePC (sampleCaller embed) (NativeCSRPositiveWitness.assignment false)) := by
  -- Use the constructive old native fixture directly; no equality between arbitrary witnesses.
  exact realizes embed sampleMemory samplePC (sampleCaller embed) decoder (NativeCSRPositiveWitness.body false)
    (by rfl) (by
      intro column member
      have slots : initializationColumns = [126,127,128,129,130,131] := NativeMainAuxiliaryProofs.initialization_geometry.2.2.2
      rw [slots] at member
      simp only [List.mem_cons,List.mem_nil_iff,or_false] at member
      rcases member with rfl|rfl|rfl|rfl|rfl|rfl <;> decide +kernel)
    (congrArg CSRRequest.multiplicity (NativeCSRBodyPaddingProofs.observations false).2) (sample_nonpoles embed)

/-- Abstract finite sum first; no evaluation of the actual eight-million-row list. -/
theorem constant_sum {R : Type} [Field R] (n : Nat) (value : R) :
    (∑ _ ∈ Finset.range n, value) = (n : R)*value := by simp

theorem request_sum {R : Type} [Field R] (embed : F →+* R) (memory : MemoryKeyChallenges R)
    (pc : PCChallenges R) (ch : CSRArgumentChallenges R) (w : Nat → F) :
    (∑ i ∈ Finset.range (callerAuxiliaryLayout.traceLength-1),
      (proof embed memory pc ch w).auxiliary i callerAuxiliaryLayout.request) =
      (8388607 : R)*(csrStageThreeArgument embed ch 1 w)⁻¹ := by
  change (∑ _ ∈ Finset.range 8388607, auxiliary embed memory pc ch w callerAuxiliaryLayout.request) = _
  have atRequest : auxiliary embed memory pc ch w callerAuxiliaryLayout.request =
      (csrStageThreeArgument embed ch 1 w)⁻¹ := by simp [auxiliary,callerAuxiliaryLayout]
  rw [atRequest,constant_sum]
  simp only [Nat.cast_ofNat]

theorem request_sum_nonzero {R : Type} [Field R] (embed : F →+* R) (memory : MemoryKeyChallenges R)
    (pc : PCChallenges R) (ch : CSRArgumentChallenges R) (w : Nat → F)
    (nonpoles : Nonpoles embed memory pc ch w) :
    (∑ i ∈ Finset.range (callerAuxiliaryLayout.traceLength-1),
      (proof embed memory pc ch w).auxiliary i callerAuxiliaryLayout.request) ≠ 0 := by
  rw [request_sum]
  have scalar : (8388607 : F) ≠ 0 := by decide +kernel
  have mapped : (8388607 : R) ≠ 0 := by
    intro zero
    apply scalar
    apply embed.injective
    have cast : embed (8388607 : F) = (8388607 : R) := by
      simpa only [Nat.cast_ofNat] using map_natCast embed 8388607
    simpa only [map_zero] using cast.trans zero
  exact mul_ne_zero mapped (inv_ne_zero nonpoles.2.2)

/-- The full caller sum rejects a zero-claim completion of THIS constant fixture.
    This is not a claimed global positive witness or a native defect. -/
theorem no_zero_claim {R : Type} [Field R] (embed : F →+* R) (memory : MemoryKeyChallenges R)
    (pc : PCChallenges R) (ch : CSRArgumentChallenges R) (w : Nat → F)
    (nonpoles : Nonpoles embed memory pc ch w) (polynomial : Polynomial R) (omega : R) :
    ¬ CallerDelegationAccepted embed ch
      ⟨(proof embed memory pc ch w).rows,(proof embed memory pc ch w).auxiliary,polynomial,omega,0⟩ := by
  intro accepted
  have sum := Airbender.ReducedMachine.NativeCallerDelegationProofs.caller_sum embed ch accepted
  exact request_sum_nonzero embed memory pc ch w nonpoles sum
end Airbender.NativeInactiveMainProofs
