import Airbender.Review.Circuits.ReducedMachine.WorkerClockProgress
import Airbender.Proofs.ReducedMachine.NativeActiveWorkerClocks
import Airbender.Proofs.Blake2Worker.NativeMemory
import Airbender.Proofs.Trace.Timestamps

namespace Airbender.NativeWorkerClockProgressProofs
open Airbender.NativeWorkerClockProgress Airbender.Verification
open Airbender.NativeInitializationBatch (Proof)
open Airbender.Blake2Worker.Native Airbender.ReducedMachine.Native Airbender.ReducedMachine.NativeMemoryBoundary
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

theorem read_time (w : Nat → F) (slot : Fin 43) :
    (readToken w slot).time = (w (memoryAccess slot).readTime[0],w (memoryAccess slot).readTime[1]) := by
  simp [readToken,Airbender.NativeMemoryTokens.encodeKey,quotientMemoryKey,keyTime]

/-- Generic checked comparison reused on ACTUAL native differences/borrows.
    Both bounds are internal to this lemma; public roots derive alternatives. -/
theorem strict_read {w : Nat → F} (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints Airbender.Blake2Worker.Fixed.table)) (slot : Fin 43)
    (active : w constraintsABI.multiplicity = 1) (current : (clock w).Bounded)
    (previous : (readClock w slot).Bounded) : (readClock w slot).value < (clock w).value := by
  have effects := Airbender.Blake2Worker.MemoryProofs.local_effects holds
  have bit := Airbender.Blake2Worker.MemoryProofs.borrow_boolean holds slot
  have low := effects.lowDifferences slot
  have high := effects.highDifferences slot
  have shape := read_time w slot
  have lower : (((readClock w slot).lo : F) - (clock w).lo - 0 +
      524288*w (clockBorrowColumn slot)).val < 524288 := by
    simpa [readClock,clock,shape,Trace.timeOfPair,Airbender.NativeActiveWorkerClocks.workerClock,
      lowClockDifference,ZMod.natCast_zmod_val] using low
  have upper : (((readClock w slot).hi : F)+524288-w (clockBorrowColumn slot)-(clock w).hi).val < 524288 := by
    simpa [readClock,clock,shape,Trace.timeOfPair,Airbender.NativeActiveWorkerClocks.workerClock,
      highClockDifference,active,ZMod.natCast_zmod_val,add_comm,sub_sub] using high
  have result := Trace.Proofs.native_port_order_of_room (p := mersenne31Modulus) (by decide)
    current previous (offset := 0) (by decide) (by simpa using current.1) bit lower upper
  simpa only [Nat.add_zero] using result

/-- Source-derived disjunction keeps unbounded cases visible, without assuming
    processor/old-read bounds or a valid initialized execution. -/
theorem local_progress {w : Nat → F} (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints Airbender.Blake2Worker.Fixed.table)) : LocalProgress w := by
  classical
  intro slot active
  by_cases current : (clock w).Bounded
  · by_cases previous : (readClock w slot).Bounded
    · exact Or.inr (Or.inr (strict_read holds slot active current previous))
    · exact Or.inr (Or.inl previous)
  · exact Or.inl current

theorem zero_unbounded {w : Nat → F} (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints Airbender.Blake2Worker.Fixed.table))
    (active : w constraintsABI.multiplicity = 1)
    (zero : Airbender.NativeActiveWorkerClocks.workerClock w = (0,0)) (slot : Fin 43) :
    ¬ (readClock w slot).Bounded := by
  intro previous
  have current : (clock w).Bounded := by
    simp only [clock,zero,Trace.timeOfPair,Trace.Timestamp.Bounded,Trace.timestampBase,ZMod.val_zero]
    omega
  have order := strict_read holds slot active current previous
  have noTime : (clock w).value = 0 := by
    simp [clock,zero,Trace.timeOfPair,Trace.Timestamp.value]
  rw [noTime] at order
  omega

/-- Exact membership in the unchanged complete memory read ledger. -/
theorem read_member {Setup R : Type} [Field R] (proofs : List (Proof R)) {batch : WorkerBatch Setup R}
    {w : Nat → F} (present : w ∈ Airbender.NativeTokenLedger.workerRows batch) (slot : Fin 43) :
    readToken w slot ∈ Airbender.NativeInitializationSeedBoundary.accessTokens proofs batch false := by
  apply List.mem_append_right
  exact List.mem_flatMap.mpr ⟨w,present,List.mem_map.mpr ⟨slot,List.mem_finRange _,rfl⟩⟩

theorem effects {Setup R : Type} [Field R] (embed : F →+* R) (memory : MemoryKeyChallenges R)
    (ch : CSRArgumentChallenges R) (pc : PCChallenges R) (gamma : R) (config : WorkerConfiguration Setup)
    {proofs : List (Proof R)} {batch : WorkerBatch Setup R} {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : Airbender.NativeInitializationBatch.Accepted embed memory ch pc gamma config proofs batch inputs inverse) :
    Effects batch := by
  classical
  have sources := Airbender.NativeActiveWorkerClockProofs.read_clocks embed memory ch pc gamma config accepted
  have unbounded : ∀ w ∈ Airbender.NativeTokenLedger.workerRows batch, ∀ slot : Fin 43,
      ¬ (readClock w slot).Bounded → UnboundedWriter batch (readToken w slot) := by
    intro w present slot previous
    exact sources.unbounded _ (read_member proofs present slot) previous
  constructor
  · intro w present active slot
    rcases local_progress (sources.processing w present).body slot active with current | previous | order
    · exact Or.inl current
    · exact Or.inr (Or.inr (unbounded w present slot previous))
    · exact Or.inr (Or.inl order)
  · intro w present active zero slot
    exact unbounded w present slot (zero_unbounded (sources.processing w present).body active zero slot)
end Airbender.NativeWorkerClockProgressProofs
