import Airbender.Review.Circuits.ReducedMachine.NativeMemoryHistoryTheorems
import Tests.NativeInitializationBatch

namespace Airbender.Tests.NativeMemoryHistory
open Airbender.NativeMemoryHistory
open Airbender.NativeMemoryHistoryProofs (row_projection matched_read empty_accesses)
open Airbender.NativeInitializationBatch (Proof)
open Airbender.ReducedMachine.Native Airbender.ReducedMachine.NativeMemoryBoundary Airbender.Blake2Worker.Native
open Airbender.Trace
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

private def inputs : PublicBoundary := ⟨fun _ => ⟨0,#v[0,0]⟩,0,#v[4,0]⟩

/-- Pure/structural/EMPTY/conditional controls, not accepted nonempty source/
    global/worker/physical witnesses or native attack/defect certificates. -/
theorem actual_empty_batch : (emptyWorkers Unit F).countWord = 0 ∧ (emptyWorkers Unit F).outputs = [] := ⟨rfl,rfl⟩

theorem same_initial_memory {R : Type} [Field R] (proofs : List (Proof R)) :
    (mainTrace proofs inputs).initialMemory = Airbender.NativeInitializationSeedBoundary.initialTokens proofs := rfl

theorem same_terminal_memory {R : Type} [Field R] (proofs : List (Proof R)) (publicInputs : PublicBoundary) :
    (mainTrace proofs publicInputs).terminalMemory = Airbender.NativeInitializationSeedBoundary.terminalTokens proofs publicInputs := rfl

theorem both_actual_port_projections (w : Nat → F) (write : Bool) :
    (([w].map fun a => (⟨.reduced,a⟩ : Row mersenne31Modulus NativeReducedFamily)).flatMap
      fun row => if write then row.writes else row.reads) = [w].flatMap (fun a => Airbender.NativeMemoryTokens.mainTokens a write) := row_projection [w] write

theorem actual_empty_accesses {R : Type} [Field R] (proofs : List (Proof R)) (publicInputs : PublicBoundary) (write : Bool) :
    Airbender.NativeInitializationSeedBoundary.accessTokens proofs (emptyWorkers Unit R) write =
      (mainTrace proofs publicInputs).rows.flatMap (fun row => if write then row.writes else row.reads) := empty_accesses proofs publicInputs write

theorem source_seed_control : (7 : Nat) ∈ [7] ∨ (7 : Nat) ∈ [] :=
  matched_read (initial := [7]) (terminal := []) (writes := []) (reads := [7]) (List.Perm.refl _) (by simp)

/-- Token-source membership by itself permits an unseeded cycle; the native
    strict-clock/history theorem supplies additional DERIVED progress. -/
theorem unseeded_loop_not_rooted : ((17 : Nat) ∈ [] ∨ (17 : Nat) ∈ [17]) ∧ (17 : Nat) ∉ ([] : List Nat) := by
  exact ⟨matched_read (initial := []) (terminal := []) (writes := [17]) (reads := [17]) (List.Perm.refl _) (by simp),by simp⟩

theorem unmatched_read_rejected : ¬ (([0] : List Nat) ++ []).Perm ([] ++ [1]) := by
  intro matching
  have source := matched_read matching (by simp : (1 : Nat) ∈ [1])
  simp at source

theorem duplicate_sources_preserved : (([0,0] : List Nat) ++ [1,1]).Perm ([] ++ [0,0,1,1]) := List.Perm.refl _

theorem all32_initial_registers_kept : (mainTrace ([] : List (Proof F)) inputs).initialMemory.length = 32 := by
  change Airbender.NativeInitializationSeedBoundary.initialRegisters.length = 32
  simp [Airbender.NativeInitializationSeedBoundary.initialRegisters]

/-- COMPLETE EMPTY existing combined component, with all32 public seed/terminal
    registers. This is not a positive nonempty main or worker witness. -/
theorem complete_empty_effects : MainEffects ([] : List (Proof F)) inputs :=
  native_main_memory_history _ _ _ _ _ _ Airbender.Tests.NativeInitializationBatch.empty_combined_component

theorem complete_empty_real_acceptance : Trace.Accepted (mainTrace ([] : List (Proof F)) inputs) := complete_empty_effects.accepted

theorem complete_empty_history : ∃ history, MemoryHistory (mainTrace ([] : List (Proof F)) inputs) history := complete_empty_effects.history

theorem complete_empty_public_image (before : Reference.RiscV.Sail.State) :
    Airbender.NativeInitializationPublicImage.Effects ([] : List (Proof F)) before := complete_empty_effects.publicImage before

private def wrongInputs : PublicBoundary := ⟨fun _ => ⟨0,#v[0,0]⟩,0,#v[8,0]⟩

theorem wrong_empty_terminal_rejected : ¬ Trace.Accepted (mainTrace ([] : List (Proof F)) wrongInputs) := by
  intro accepted
  have states := accepted.states
  change ([Airbender.NativeMainStateHistory.state initialPCKey] : List (PCState.State mersenne31Modulus)).Perm
    [Airbender.NativeMainStateHistory.state (finalPCKey wrongInputs)] at states
  have equal := List.mem_singleton.mp (states.mem_iff.mp (List.mem_cons_self))
  have clocks := congrArg (fun point : PCState.State mersenne31Modulus => point.timestamp.1) equal
  change (4 : F) = 8 at clocks
  exact (by decide +kernel : (4 : F) ≠ 8) clocks

theorem full_conditional_read_sources {Setup R : Type} [Field R] (embed : F →+* R) (memory : MemoryKeyChallenges R)
    (ch : CSRArgumentChallenges R) (pc : PCChallenges R) (gamma : R) (config : WorkerConfiguration Setup)
    {proofs : List (Proof R)} {batch : WorkerBatch Setup R} {publicInputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : Airbender.NativeInitializationBatch.Accepted embed memory ch pc gamma config proofs batch publicInputs inverse) :
    ReadEffects proofs batch := native_actual_read_sources embed memory ch pc gamma config accepted

theorem full_conditional_main_history {Setup R : Type} [Field R] (embed : F →+* R) (memory : MemoryKeyChallenges R)
    (ch : CSRArgumentChallenges R) (pc : PCChallenges R) (gamma : R) (config : WorkerConfiguration Setup)
    {proofs : List (Proof R)} {publicInputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : Airbender.NativeInitializationBatch.Accepted embed memory ch pc gamma config proofs (emptyWorkers Setup R) publicInputs inverse) :
    MainEffects proofs publicInputs := native_main_memory_history embed memory ch pc gamma config accepted

end Airbender.Tests.NativeMemoryHistory
