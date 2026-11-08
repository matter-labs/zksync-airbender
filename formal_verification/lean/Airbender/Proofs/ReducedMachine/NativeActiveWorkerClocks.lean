import Airbender.Review.Circuits.ReducedMachine.ActiveWorkerClocks
import Airbender.Proofs.ReducedMachine.NativeMemoryHistory
import Airbender.Proofs.Blake2Worker.NativeCapacity
import Airbender.Proofs.Blake2Worker.NativeMemoryKeys

namespace Airbender.NativeActiveWorkerClockProofs
open Airbender.NativeActiveWorkerClocks
open Airbender.NativeInitializationBatch (Proof)
open Airbender.Blake2Worker.Native Airbender.ReducedMachine.Native Airbender.ReducedMachine.NativeMemoryBoundary
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- Generic finite source sampling BEFORE native domain instantiation. -/
theorem sampled_property {A B : Type} (items : List A) (rows : A → Nat → B) (count : Nat) (property : B → Prop)
    (holds : ∀ item ∈ items, ∀ i < count, property (rows item i)) :
    ∀ value ∈ items.flatMap (fun item => (List.range count).map (rows item)), property value := by
  intro value member
  obtain ⟨item,present,source⟩ := List.mem_flatMap.mp member
  obtain ⟨i,ordinary,rfl⟩ := List.mem_map.mp source
  exact holds item present i (List.mem_range.mp ordinary)

/-- Full configured source acceptance on EACH actual ordinary worker row. -/
theorem worker_processing {Setup R : Type} [Field R] (embed : F →+* R) (memory : MemoryKeyChallenges R)
    (ch : CSRArgumentChallenges R) (pc : PCChallenges R) (gamma : R) (config : WorkerConfiguration Setup)
    {proofs : List (Proof R)} {batch : WorkerBatch Setup R} {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : Airbender.NativeInitializationBatch.Accepted embed memory ch pc gamma config proofs batch inputs inverse) :
    ∀ w ∈ Airbender.NativeTokenLedger.workerRows batch, LocalProcessingAccepted w := by
  have source : ∀ output ∈ batch.outputs, ∀ i < constraintsABI.traceLength-1, LocalProcessingAccepted (output.proof.rows i) := by
    intro output member i bound
    exact ((Airbender.Blake2Worker.CapacityProofs.shared_acceptance embed memory (workerProcessorChallenges ch) config
      accepted.arguments.globalMemory.workers output member).trace.rows i bound).body
  exact sampled_property batch.outputs (fun output => output.proof.rows) (constraintsABI.traceLength-1) LocalProcessingAccepted source

/-- Every raw write uses the SAME two actual processing-clock fields. -/
theorem write_clock (w : Nat → F) (slot : Fin 43) :
    (Airbender.NativeMemoryTokens.encodeKey (quotientMemoryKey w slot true)).time = workerClock w := by
  simp [Airbender.NativeMemoryTokens.encodeKey,quotientMemoryKey,keyTime,workerClock]

/-- Reuse the existing accepted processing zero-mask theorem; no auxiliary
    value or pole is removed. Both raw clock fields are ACTUALLY zero when m0. -/
theorem padding_clock {w : Nat → F} (effects : ProcessingEffects w) (zero : w constraintsABI.multiplicity = 0) :
    workerClock w = (0,0) := by
  have time := Airbender.Blake2Worker.MemoryKeyProofs.padding_time effects zero (0 : Fin 43) true
  rw [← write_clock w (0 : Fin 43)]
  change ((keyTime w 0 true)[0],(keyTime w 0 true)[1]) = (0,0)
  rw [time]
  rfl

theorem bounded_or_active {w : Nat → F} (accepted : LocalProcessingAccepted w) :
    (Trace.timeOfPair (workerClock w)).Bounded ∨ w constraintsABI.multiplicity = 1 := by
  have effects := Airbender.Blake2Worker.ProcessingProofs.effects accepted.conventions
  rcases effects.multiplicityBit with zero | active
  · left
    rw [padding_clock effects zero]
    constructor <;> decide +kernel
  · exact Or.inr active

/-- Source membership preserves exact tokens and duplicate occurrences. -/
theorem source_slot {Setup R : Type} [Field R] {batch : WorkerBatch Setup R} {token : Trace.MemoryToken mersenne31Modulus}
    (member : token ∈ Airbender.NativeMemoryHistory.workerWrites batch) :
    ∃ w ∈ Airbender.NativeTokenLedger.workerRows batch, ∃ slot : Fin 43,
      Airbender.NativeMemoryTokens.encodeKey (quotientMemoryKey w slot true) = token := by
  obtain ⟨w,present,source⟩ := List.mem_flatMap.mp member
  obtain ⟨slot,_,same⟩ := List.mem_map.mp source
  exact ⟨w,present,slot,same⟩

theorem active_writer_member {Setup R : Type} [Field R] {batch : WorkerBatch Setup R}
    {token : Trace.MemoryToken mersenne31Modulus} (source : ActiveWriter batch token) :
    token ∈ Airbender.NativeMemoryHistory.workerWrites batch := by
  obtain ⟨w,present,slot,_,same,_⟩ := source
  subst token
  exact List.mem_flatMap.mpr ⟨w,present,List.mem_map.mpr ⟨slot,List.mem_finRange _,rfl⟩⟩

/-- Generic final implication does not construct a history or assume rooting. -/
theorem unbounded_source {Setup R : Type} [Field R] {batch : WorkerBatch Setup R} {token : Trace.MemoryToken mersenne31Modulus}
    (source : (Trace.timeOfPair token.time).Bounded ∨ ActiveWriter batch token)
    (unbounded : ¬ (Trace.timeOfPair token.time).Bounded) :
    ∃ w ∈ Airbender.NativeTokenLedger.workerRows batch, ∃ slot : Fin 43,
      w constraintsABI.multiplicity = 1 ∧
        token = Airbender.NativeMemoryTokens.encodeKey (quotientMemoryKey w slot true) ∧
        token.time = workerClock w ∧ ¬ (Trace.timeOfPair (workerClock w)).Bounded := by
  obtain ⟨w,present,slot,active,same,clock⟩ := source.resolve_left unbounded
  exact ⟨w,present,slot,active,same,clock,by simpa only [← clock] using unbounded⟩

theorem read_clocks {Setup R : Type} [Field R] (embed : F →+* R) (memory : MemoryKeyChallenges R)
    (ch : CSRArgumentChallenges R) (pc : PCChallenges R) (gamma : R) (config : WorkerConfiguration Setup)
    {proofs : List (Proof R)} {batch : WorkerBatch Setup R} {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : Airbender.NativeInitializationBatch.Accepted embed memory ch pc gamma config proofs batch inputs inverse) :
    Effects proofs batch := by
  have processing := worker_processing embed memory ch pc gamma config accepted
  have reads := Airbender.NativeMemoryHistoryProofs.full_read_sources embed memory ch pc gamma config accepted
  have clocks : ∀ token ∈ Airbender.NativeInitializationSeedBoundary.accessTokens proofs batch false,
      (Trace.timeOfPair token.time).Bounded ∨ ActiveWriter batch token := by
    intro token member
    rcases reads.clocks token member with bounded | written
    · exact Or.inl bounded
    · obtain ⟨w,present,slot,same⟩ := source_slot written
      rcases bounded_or_active (processing w present) with bounded | active
      · left
        rw [← same,write_clock]
        exact bounded
      · exact Or.inr ⟨w,present,slot,active,same.symm,by rw [← same,write_clock]⟩
  exact ⟨processing,clocks,fun token member => unbounded_source (clocks token member)⟩

end Airbender.NativeActiveWorkerClockProofs
