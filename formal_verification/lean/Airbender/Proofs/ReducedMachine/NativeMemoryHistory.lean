import Airbender.Review.Circuits.ReducedMachine.NativeMemoryHistory
import Airbender.Proofs.ReducedMachine.NativeInitializationPublicImage
import Airbender.Proofs.ReducedMachine.NativeInitializationBatch
import Airbender.Proofs.Trace.MemoryHistory
import Airbender.Proofs.Trace.LatestReads

namespace Airbender.NativeMemoryHistoryProofs
open Airbender.NativeMemoryHistory Airbender.Trace
open Airbender.NativeInitializationBatch (Proof mainProofs)
open Airbender.NativeInitializationSeedBoundary (initialTokens terminalTokens accessTokens)
open Airbender.ReducedMachine.Native Airbender.ReducedMachine.NativeMemoryBoundary Airbender.Blake2Worker.Native
abbrev F := ZMod mersenne31Modulus
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- Entire abstract list projection BEFORE native domain instantiation. -/
theorem row_projection (assignments : List (Nat → F)) (write : Bool) :
    ((assignments.map fun w => (⟨.reduced,w⟩ : Row mersenne31Modulus NativeReducedFamily)).flatMap
      fun row => if write then row.writes else row.reads) =
        assignments.flatMap (fun w => Airbender.NativeMemoryTokens.mainTokens w write) := by
  rw [List.flatMap_map]
  cases write <;> rfl

theorem main_projection {R : Type} [Field R] (proofs : List (Proof R)) (write : Bool) :
    ((Airbender.NativeMainStateHistory.rows (mainProofs proofs)).flatMap fun row => if write then row.writes else row.reads) =
      (Airbender.NativeMainStateHistory.selectAssignments (Airbender.NativeTokenLedger.mainRows (mainProofs proofs))).flatMap
        (fun w => Airbender.NativeMemoryTokens.mainTokens w write) := row_projection _ write

/-- A matched read has an EXACT seed or write token, including address/value/
    both raw timestamp limbs. This alone does not prove clock order or rooting. -/
theorem matched_read {A : Type} {initial terminal writes reads : List A}
    (matching : (initial ++ writes).Perm (terminal ++ reads)) {token : A} (member : token ∈ reads) :
    token ∈ initial ∨ token ∈ writes :=
  List.mem_append.mp (matching.mem_iff.mpr (List.mem_append_right _ member))

theorem selected_active (assignments : List (Nat → F)) :
    ∀ row ∈ (Airbender.NativeMainStateHistory.selectAssignments assignments).map
      (fun w => (⟨.reduced,w⟩ : Row mersenne31Modulus NativeReducedFamily)), row.assignment row.columns.execute = 1 := by
  intro row member
  obtain ⟨w,present,rfl⟩ := List.mem_map.mp member
  exact of_decide_eq_true (List.mem_filter.mp present).2

theorem components {Setup R : Type} [Field R] (embed : F →+* R) (memory : MemoryKeyChallenges R)
    (ch : CSRArgumentChallenges R) (pc : PCChallenges R) (gamma : R) (config : WorkerConfiguration Setup)
    {proofs : List (Proof R)} {batch : WorkerBatch Setup R} {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : Airbender.NativeInitializationBatch.Accepted embed memory ch pc gamma config proofs batch inputs inverse) :
    ∀ proof ∈ mainProofs proofs, Airbender.ReducedMachine.NativeMainAuxiliary.Accepted embed memory pc proof := by
  intro proof member
  obtain ⟨origin,present,rfl⟩ := List.mem_map.mp member
  exact accepted.arguments.mainMemory origin.main (List.mem_map.mpr ⟨origin,present,rfl⟩)

theorem full_read_sources {Setup R : Type} [Field R] (embed : F →+* R) (memory : MemoryKeyChallenges R)
    (ch : CSRArgumentChallenges R) (pc : PCChallenges R) (gamma : R) (config : WorkerConfiguration Setup)
    {proofs : List (Proof R)} {batch : WorkerBatch Setup R} {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : Airbender.NativeInitializationBatch.Accepted embed memory ch pc gamma config proofs batch inputs inverse) :
    ReadEffects proofs batch := by
  have seeds := Airbender.NativeInitializationSeedBoundaryProofs.boundary embed memory ch pc gamma config accepted
  have state := Airbender.NativeMainStateHistoryProofs.history embed memory pc
    (components embed memory ch pc gamma config accepted) accepted.matching
  have matching := Airbender.NativeInitializationSeedBoundaryProofs.memory_matching accepted.matching
  have source : ∀ token ∈ accessTokens proofs batch false,
      token ∈ initialTokens proofs ∨ token ∈ mainWrites proofs ∨ token ∈ workerWrites batch := by
    intro token member
    have origin := matched_read matching member
    rcases origin with seed | written
    · exact Or.inl seed
    · right
      unfold accessTokens at written
      rw [← main_projection proofs true] at written
      exact List.mem_append.mp written
  refine ⟨source,?_⟩
  intro token member
  rcases source token member with seed | main | worker
  · left
    rw [seeds.clocks token seed]
    constructor <;> decide +kernel
  · left
    obtain ⟨row,present,portMember⟩ := List.mem_flatMap.mp main
    obtain ⟨port,actual,rfl⟩ := List.mem_map.mp portMember
    exact (state.writes row present port (by simpa using actual)).1
  · exact Or.inr worker

/-- Actual batch observation is empty BY CONSTRUCTION, not by a list-equality
    premise. No original worker proof/auxiliary acceptance is weakened. -/
theorem empty_accesses {Setup R : Type} [Field R] (proofs : List (Proof R)) (inputs : PublicBoundary) (write : Bool) :
    accessTokens proofs (emptyWorkers Setup R) write =
      (mainTrace proofs inputs).rows.flatMap (fun row => if write then row.writes else row.reads) := by
  change accessTokens proofs (emptyWorkers Setup R) write =
    (Airbender.NativeMainStateHistory.rows (mainProofs proofs)).flatMap _
  rw [main_projection]
  simp only [accessTokens,emptyWorkers,Airbender.NativeTokenLedger.workerRows,List.flatMap_nil,List.append_nil]

theorem trace_accepted {Setup R : Type} [Field R] (embed : F →+* R) (memory : MemoryKeyChallenges R)
    (ch : CSRArgumentChallenges R) (pc : PCChallenges R) (gamma : R) (config : WorkerConfiguration Setup)
    {proofs : List (Proof R)} {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : Airbender.NativeInitializationBatch.Accepted embed memory ch pc gamma config proofs (emptyWorkers Setup R) inputs inverse) :
    Trace.Accepted (mainTrace proofs inputs) := by
  have source := components embed memory ch pc gamma config accepted
  have states := Airbender.NativeMainStateHistoryProofs.history embed memory pc source accepted.matching
  have matching := Airbender.NativeInitializationSeedBoundaryProofs.memory_matching accepted.matching
  refine ⟨Airbender.NativeMainStateHistoryProofs.selected_body embed memory pc _ source,
    selected_active _,states.states,?_⟩
  rw [empty_accesses proofs inputs true,empty_accesses proofs inputs false] at matching
  exact matching

theorem clock_boundary {Setup R : Type} [Field R] (embed : F →+* R) (memory : MemoryKeyChallenges R)
    (ch : CSRArgumentChallenges R) (pc : PCChallenges R) (gamma : R) (config : WorkerConfiguration Setup)
    {proofs : List (Proof R)} {batch : WorkerBatch Setup R} {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : Airbender.NativeInitializationBatch.Accepted embed memory ch pc gamma config proofs batch inputs inverse) :
    ClockBoundary (mainTrace proofs inputs) := by
  have seeds := Airbender.NativeInitializationSeedBoundaryProofs.boundary embed memory ch pc gamma config accepted
  have initial := Airbender.NativeMainStateHistoryProofs.initial_clock
  refine ⟨?_,?_,?_⟩
  · change (timeOfPair (Airbender.NativeMainStateHistory.state initialPCKey).timestamp).Bounded
    rw [initial]
    constructor <;> decide +kernel
  · change (timeOfPair (Airbender.NativeMainStateHistory.state initialPCKey).timestamp).value % 4 = 0
    rw [initial]
    decide +kernel
  · intro token member
    rw [seeds.clocks token member]
    constructor <;> decide +kernel

theorem main_history {Setup R : Type} [Field R] (embed : F →+* R) (memory : MemoryKeyChallenges R)
    (ch : CSRArgumentChallenges R) (pc : PCChallenges R) (gamma : R) (config : WorkerConfiguration Setup)
    {proofs : List (Proof R)} {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : Airbender.NativeInitializationBatch.Accepted embed memory ch pc gamma config proofs (emptyWorkers Setup R) inputs inverse) :
    MainEffects proofs inputs := by
  have native := trace_accepted embed memory ch pc gamma config accepted
  have boundary := clock_boundary embed memory ch pc gamma config accepted
  have seeds := Airbender.NativeInitializationSeedBoundaryProofs.boundary embed memory ch pc gamma config accepted
  have bounds := Trace.Proofs.clock_inputs (by decide : 2*timestampBase+4 < mersenne31Modulus) native boundary
  refine ⟨native,boundary,seeds.addresses,?_,
    Trace.Proofs.latest_reads (by decide) native boundary seeds.addresses,
    Trace.Proofs.initialized_addresses (by decide) native boundary,
    Trace.Proofs.native_memory_paths (by decide) native boundary seeds.addresses,
    Trace.Proofs.native_memory_history (by decide) native boundary seeds.addresses,
    fun before => Airbender.NativeInitializationPublicImageProofs.public_image before seeds⟩
  intro row member port actual
  have previous := (bounds row member).previous port.clock (by
    rw [← Trace.Proofs.ports_clocks row]
    exact Array.mem_map.mpr ⟨port,actual,rfl⟩)
  exact previous

end Airbender.NativeMemoryHistoryProofs
