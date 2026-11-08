import Airbender.Review.Circuits.ReducedMachine.InitializationBatchTheorems
import Tests.NativeScalar16Arguments
import Tests.NativeMainStateHistory

namespace Airbender.Tests.NativeInitializationBatch
open Airbender.NativeInitializationBatch Airbender.NativeInitializationBatchProofs
open Airbender.ReducedMachine.Native Airbender.ReducedMachine.NativeMainAuxiliary
open Airbender.ReducedMachine.NativeMemoryBoundary Airbender.Blake2Worker.Native
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

/-- Observation DATA only, not accepted nonempty main/source/global proof. -/
private noncomputable def observed : Proof F :=
  let old := Airbender.Tests.NativeScalar16Arguments.observed
  ⟨⟨old.initialization.main,0,0,2⟩,old.initialization.base,old.witness,old.setup,old.polynomial,old.omega,
    ⟨#v[0,0,0,0,0,0],#v[0,0,0,0,0,0]⟩⟩

theorem actual_same_main (proof : Proof F) : proof.scalar.initialization.main = proof.main.memory := scalar_main proof

theorem actual_same_auxiliary (proof : Proof F) :
    proof.scalar.initialization.main.auxiliary = proof.main.caller.auxiliary := rfl

theorem actual_same_caller_rows (proof : Proof F) :
    proof.scalar.initialization.main.rows = proof.main.caller.rows := rfl

theorem retained_observations : observed.scalar.witness 0 scalar16Layout.multiplicity = 23 ∧
    observed.scalar.initialization.base 0 initializationRangeLayout.product = 4 ∧
    observed.scalar.setup 0 scalar16Layout.setup = 0 := ⟨rfl,rfl,rfl⟩

theorem distinct_claims_retained : observed.main.memory.grandClaim = 1 ∧ observed.main.caller.delegationClaim = 2 := ⟨rfl,rfl⟩

theorem same_actual_list {R : Type} [Field R] (proofs : List (Proof R)) :
    mainProofs proofs = (mainArguments proofs).map (fun proof => proof.memory) := same_list proofs

theorem both_sides_full_ledger {Setup R : Type} [Field R] (proofs : List (Proof R)) (batch : WorkerBatch Setup R)
    (inputs : PublicBoundary) {proof : Proof R} (member : proof ∈ proofs)
    (i : Nat) (bound : i < scalar16Layout.traceLength-1) :
    Airbender.NativeTokenLedger.Token.memory (initializationToken proof i false) ∈
      Airbender.NativeTokenLedger.fullTokens (mainProofs proofs) batch inputs false ∧
    Airbender.NativeTokenLedger.Token.memory (initializationToken proof i true) ∈
      Airbender.NativeTokenLedger.fullTokens (mainProofs proofs) batch inputs true :=
  ⟨native_same_main_initialization_tokens proofs batch inputs member i bound false,
    native_same_main_initialization_tokens proofs batch inputs member i bound true⟩

theorem last_ordinary_token_kept {Setup : Type} (batch : WorkerBatch Setup F) (inputs : PublicBoundary) :
    Airbender.NativeTokenLedger.Token.memory (initializationToken observed (scalar16Layout.traceLength-2) true) ∈
      Airbender.NativeTokenLedger.fullTokens (mainProofs [observed]) batch inputs true :=
  native_same_main_initialization_tokens [observed] batch inputs (by simp) _ (by decide +kernel) true

private def inputs : PublicBoundary := ⟨fun _ => ⟨0,#v[0,0]⟩,0,#v[4,0]⟩
private def memory : MemoryKeyChallenges F := ⟨0,0,0,0,0,0,0⟩
private def pc : PCChallenges F := ⟨1,0,0,0⟩
private def ch : CSRArgumentChallenges F := ⟨0,0,0,0⟩
private def config : WorkerConfiguration Unit := ⟨.security80,()⟩
private def batch : WorkerBatch Unit F := ⟨0,[]⟩
private def inverse : BoundaryInverses F := ⟨1,1⟩

/-- COMPLETE EMPTY stronger selected component. Not a nonempty main/worker/
    source/physical verifier witness. Full public registers/PC remain. -/
theorem empty_combined_component : Accepted (RingHom.id F) memory ch pc 1 config [] batch inputs inverse := by
  constructor
  · constructor
    · simp [mainArguments]
    · simp [mainArguments]
    · exact Airbender.Tests.NativeMainStateHistory.empty_component.global
    · rfl
  · simp
  · intro c bound; simp at bound
  · exact Airbender.Tests.NativeMainStateHistory.empty_full_logical_matching

theorem empty_joint_terminal :
    (Trace.timeOfPair (Airbender.NativeMainStateHistory.state (finalPCKey inputs)).timestamp).value = 4 := by
  have effects := native_same_main_initialization (RingHom.id F) memory ch pc 1 config empty_combined_component
  simpa [mainProofs,Airbender.NativeMainStateHistory.rows,Airbender.NativeMainStateHistory.selectAssignments,
    Airbender.NativeTokenLedger.mainRows] using effects.2.1.terminal

theorem wrong_empty_terminal_rejected : ¬ Accepted (RingHom.id F) memory ch pc 1 config ([] : List (Proof F)) batch
    {inputs with finalTime := #v[8,0]} inverse := by
  intro accepted
  have effects := native_same_main_initialization (RingHom.id F) memory ch pc 1 config accepted
  exact Airbender.Tests.NativeMainStateHistory.wrong_empty_terminal_rejected effects.2.1

theorem complete_conditional_joint {Setup R : Type} [Field R] (embed : F →+* R) (mem : MemoryKeyChallenges R)
    (call : CSRArgumentChallenges R) (state : PCChallenges R) (gamma : R) (cfg : WorkerConfiguration Setup)
    {proofs : List (Proof R)} {workers : WorkerBatch Setup R} {publicInputs : PublicBoundary} {inverses : BoundaryInverses R}
    (accepted : Accepted embed mem call state gamma cfg proofs workers publicInputs inverses) :
    Airbender.ReducedMachine.NativeMainArguments.Effects embed mem state (mainArguments proofs) workers publicInputs ∧
      Airbender.NativeMainStateHistory.Effects (mainProofs proofs) publicInputs ∧ InitializationEffects proofs :=
  native_same_main_initialization embed mem call state gamma cfg accepted

end Airbender.Tests.NativeInitializationBatch
