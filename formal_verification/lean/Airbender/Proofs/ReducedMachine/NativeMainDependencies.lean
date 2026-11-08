import Airbender.Review.Circuits.ReducedMachine.MainDependencies
import Airbender.Proofs.ReducedMachine.NativeWorkerWriteWords
import Airbender.Proofs.ReducedMachine.NativeWordMemoryAccess

namespace Airbender.NativeMainDependencyProofs
open Airbender.NativeMainDependencies
open Airbender.ReducedMachine.Native Airbender.ReducedMachine.NativeMemoryBoundary
open Airbender.Blake2Worker.Native Verification
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

/-- Bounded main write clocks agree with the old signed proof measure. This is
    a derived equality of measures, never a replacement raw timestamp encoding. -/
theorem bounded_rank (token : Airbender.NativeMixedMemoryOrder.Token)
    (bounded : (Trace.timeOfPair token.time).Bounded) :
    Airbender.NativeCompleteMemoryPaths.rank token = (Trace.timeOfPair token.time).value := by
  change token.time.1.val < 524288 ∧ token.time.2.val < 524288 at bounded
  have low : token.time.1 ≠ -1 := by
    intro same
    have large := (Airbender.NativeWorkerSignedClockProofs.sentinel token.time.1).mp same
    change token.time.1.val = 2147483646 at large
    omega
  have high : token.time.2 ≠ -1 := by
    intro same
    have large := (Airbender.NativeWorkerSignedClockProofs.sentinel token.time.2).mp same
    change token.time.2.val = 2147483646 at large
    omega
  have measure : Airbender.NativeWorkerSignedClocks.value token.time =
      ((Trace.timeOfPair token.time).value : Int) := by
    simp [Airbender.NativeWorkerSignedClocks.value,Airbender.NativeWorkerSignedClocks.limb,
      low,high,Trace.timeOfPair,Trace.Timestamp.value,Trace.timestampBase]
  simp [Airbender.NativeCompleteMemoryPaths.rank,measure]

/-- Pure actual port metadata before witness evaluation. -/
theorem readonly_values (w : Nat → F) (slot : Fin 3) (first : slot.val < 2) :
    writeWord w slot = readWord w slot := by
  fin_cases slot <;> simp [writeWord,readWord,port,importedConstraintsMemoryPorts] at *

/-- Reuse the unchanged abstract-table store proof on the SAME full BODY.
    No RuntimePool-to-Fixed transfer or decoder onehot premise is used. -/
theorem local_effects {setup : Table F (fields 4)} {w : Nat → F}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup)) : LocalEffects w := by
  refine ⟨readonly_values w,?_⟩
  intro mask
  have actual := (Airbender.ReducedMachine.NativeWordMemoryAccessProofs.store_access holds mask).written
  simpa [writeWord,readWord,port,importedConstraintsMemoryPorts,Trace.WordColumns.evaluate] using actual

private theorem port_member (row : MainRow) (slot : Fin 3) : port slot ∈ row.ports := by
  cases row with
  | mk family w =>
    cases family
    change port slot ∈ importedConstraintsMemoryPorts
    fin_cases slot <;> simp [port,importedConstraintsMemoryPorts]

private theorem offset (slot : Fin 3) : (port slot).clock.offset = slot.val := by
  fin_cases slot <;> rfl

private theorem actual_write (row : MainRow) (slot : Fin 3) :
    Trace.writeToken row.columns row.assignment (port slot) = write row.assignment slot := by
  cases row with
  | mk family w => cases family; rfl

private theorem step {Setup R : Type} [Field R]
    (proofs : List (Airbender.NativeInitializationBatch.Proof R)) (batch : WorkerBatch Setup R)
    {row : MainRow} (member : row ∈ Airbender.NativeMixedMemoryOrder.mainRows proofs) (slot : Fin 3) :
    Airbender.NativeMixedMemoryOrder.Step proofs batch (read row.assignment slot) (write row.assignment slot) :=
  Or.inl ⟨row,member,port slot,port_member row slot,rfl,(actual_write row slot).symm⟩

theorem effects {Setup R : Type} [Field R] (embed : F →+* R) (memory : MemoryKeyChallenges R)
    (ch : CSRArgumentChallenges R) (pc : PCChallenges R) (gamma : R) (config : WorkerConfiguration Setup)
    {proofs : List (Airbender.NativeInitializationBatch.Proof R)} {batch : WorkerBatch Setup R}
    {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : Airbender.NativeInitializationBatch.Accepted embed memory ch pc gamma config proofs batch inputs inverse)
    (identity : Airbender.NativeDelegationSupport.SourceIdentity proofs batch) : Effects proofs batch inputs := by
  have workers := Airbender.NativeWorkerWriteWordProofs.effects embed memory ch pc gamma config accepted identity
  have components := Airbender.NativeMemoryHistoryProofs.components embed memory ch pc gamma config accepted
  have state := Airbender.NativeMainStateHistoryProofs.history embed memory pc components accepted.matching
  have body := Airbender.NativeMainStateHistoryProofs.selected_body embed memory pc _ components
  have writes : ∀ row ∈ Airbender.NativeMixedMemoryOrder.mainRows proofs, ∀ slot,
      Airbender.NativeCompleteMemoryPaths.rank (write row.assignment slot) = row.clock+slot.val := by
    intro row member slot
    have clock := state.writes row member (port slot) (port_member row slot)
    rw [actual_write] at clock
    rw [bounded_rank _ clock.1,clock.2,offset]
  refine ⟨workers,?_,writes,?_,?_⟩
  · intro row member
    have holds := body row member
    cases row with
    | mk family w => cases family; exact local_effects holds
  · intro row member slot
    exact (workers.prior.latest.reads _ _ (step proofs batch member slot)).source
  · intro row member source target earlier
    have previous := (workers.prior.latest.reads _ _ (step proofs batch member source)).before
    rw [writes row member source] at previous
    rw [writes row member target]
    omega

theorem counted {Setup R : Type} [Field R] (embed : F →+* R) (memory : MemoryKeyChallenges R)
    (ch : CSRArgumentChallenges R) (pc : PCChallenges R) (gamma : R) (config : WorkerConfiguration Setup)
    {batch : Airbender.NativeMainBatch.Batch R} {workers : WorkerBatch Setup R}
    {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : Airbender.NativeMainBatch.SourceAccepted embed memory ch pc gamma config batch workers inputs inverse)
    (identity : Airbender.NativeDelegationSupport.SourceIdentity batch.proofs workers) :
    Airbender.NativeMainBatch.Effects batch ∧ Effects batch.proofs workers inputs :=
  ⟨Airbender.NativeMainBatchProofs.effects batch accepted.counter,
    effects embed memory ch pc gamma config accepted.component identity⟩
end Airbender.NativeMainDependencyProofs
