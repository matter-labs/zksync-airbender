import Airbender.Review.Circuits.ReducedMachine.MixedMemoryOrderTheorems
import Tests.NativeCSRPositive

namespace Airbender.Tests.NativeMixedMemoryOrder
open Airbender.NativeMixedMemoryOrder Airbender.Verification
open Airbender.ReducedMachine.Native Airbender.Blake2Worker.Native
open Airbender.ReducedMachine.NativeMemoryBoundary
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

/-- Structural observed-edge controls, not accepted nonempty native sources. -/
theorem main_edge {Setup R : Type} [Field R]
    {proofs : List (Airbender.NativeInitializationBatch.Proof R)} (batch : WorkerBatch Setup R)
    {row : MainRow} (member : row ∈ mainRows proofs) {port : Trace.MemoryPort} (actual : port ∈ row.ports) :
    Step proofs batch (Trace.readToken row.assignment port) (Trace.writeToken row.columns row.assignment port) :=
  Or.inl ⟨row,member,port,actual,rfl,rfl⟩

theorem worker_edge {Setup R : Type} [Field R]
    (proofs : List (Airbender.NativeInitializationBatch.Proof R)) {batch : WorkerBatch Setup R}
    {w : Nat → F} (member : w ∈ Airbender.NativeTokenLedger.workerRows batch)
    (active : w constraintsABI.multiplicity = 1) (slot : Fin 43) :
    Step proofs batch (Airbender.NativeWorkerClockProgress.readToken w slot)
      (Airbender.NativeMemoryTokens.encodeKey (quotientMemoryKey w slot true)) :=
  Or.inr ⟨w,member,active,slot,rfl,rfl⟩

theorem main_read_retained {Setup R : Type} [Field R]
    (proofs : List (Airbender.NativeInitializationBatch.Proof R)) (batch : WorkerBatch Setup R)
    {row : MainRow} (member : row ∈ mainRows proofs) {port : Trace.MemoryPort} (actual : port ∈ row.ports) :
    Trace.readToken row.assignment port ∈ Airbender.NativeInitializationSeedBoundary.accessTokens proofs batch false :=
  Airbender.NativeMixedMemoryOrderProofs.main_read_member proofs batch member actual

theorem worker_read_retained {Setup R : Type} [Field R]
    (proofs : List (Airbender.NativeInitializationBatch.Proof R)) {batch : WorkerBatch Setup R}
    {w : Nat → F} (member : w ∈ Airbender.NativeTokenLedger.workerRows batch) (slot : Fin 43) :
    Airbender.NativeWorkerClockProgress.readToken w slot ∈ Airbender.NativeInitializationSeedBoundary.accessTokens proofs batch false :=
  Airbender.NativeWorkerClockProgressProofs.read_member proofs member slot

theorem inactive_worker_read_retained {Setup R : Type} [Field R]
    (proofs : List (Airbender.NativeInitializationBatch.Proof R)) {batch : WorkerBatch Setup R}
    {w : Nat → F} (member : w ∈ Airbender.NativeTokenLedger.workerRows batch)
    (inactive : w constraintsABI.multiplicity = 0) (slot : Fin 43) :
    w constraintsABI.multiplicity = 0 ∧
      Airbender.NativeWorkerClockProgress.readToken w slot ∈ Airbender.NativeInitializationSeedBoundary.accessTokens proofs batch false :=
  ⟨inactive,worker_read_retained proofs member slot⟩

theorem edge_read_retained {Setup R : Type} [Field R]
    {proofs : List (Airbender.NativeInitializationBatch.Proof R)} {batch : WorkerBatch Setup R}
    {read write : Token} (edge : Step proofs batch read write) :
    read ∈ Airbender.NativeInitializationSeedBoundary.accessTokens proofs batch false :=
  Airbender.NativeMixedMemoryOrderProofs.step_read_member edge

/-- Existing complete LOCAL117eq22lookup body, not a new global witness. -/
theorem local_body (active : Bool) : FlatOperation.ConstraintsHoldFlat
    (environment (Airbender.Tests.NativeCSRPositive.nativeRow active).assignment)
    (importedConstraints Airbender.ReducedMachine.NativeRuntimePool.table) :=
  Airbender.ReducedMachine.NativeCSRPositiveWitness.body active

theorem inactive_local_still_requests :
    (Airbender.Tests.NativeCSRPositive.nativeRow false).assignment importedConstraintsTraceColumns.execute = 0 ∧
      csrRequest (Airbender.Tests.NativeCSRPositive.nativeRow false).assignment = ⟨1,1991,some 0,3⟩ :=
  Airbender.Tests.NativeCSRPositive.inactive_body_still_requests.2

theorem local_three_port_progress (active : Bool) (port : Trace.MemoryPort) (member : port ∈ importedConstraintsMemoryPorts) :
    Airbender.NativeWorkerSignedClocks.value (Trace.readToken (Airbender.Tests.NativeCSRPositive.nativeRow active).assignment port).time <
      Airbender.NativeWorkerSignedClocks.value (Trace.writeToken importedConstraintsTraceColumns
        (Airbender.Tests.NativeCSRPositive.nativeRow active).assignment port).time := by
  apply Airbender.NativeMixedMemoryOrderProofs.main_port_progress (local_body active) port member
  · simp [importedConstraintsMemoryPorts] at member
    rcases member with rfl | rfl | rfl <;> cases active <;> constructor <;> decide +kernel
  · simp [importedConstraintsMemoryPorts] at member
    rcases member with rfl | rfl | rfl <;> cases active <;> constructor <;> decide +kernel

theorem inactive_local_not_selected {R : Type} [Field R] (proofs : List (Airbender.NativeInitializationBatch.Proof R)) :
    Airbender.Tests.NativeCSRPositive.nativeRow false ∉ mainRows proofs := by
  intro member
  have active := Airbender.NativeMemoryHistoryProofs.selected_active
    (Airbender.NativeTokenLedger.mainRows (Airbender.NativeInitializationBatch.mainProofs proofs))
    (Airbender.Tests.NativeCSRPositive.nativeRow false) member
  have inactive := inactive_local_still_requests.1
  change (Airbender.Tests.NativeCSRPositive.nativeRow false).assignment importedConstraintsTraceColumns.execute = 1 at active
  rw [inactive] at active
  exact zero_ne_one active

theorem self_step_rejected {Setup R : Type} [Field R]
    {proofs : List (Airbender.NativeInitializationBatch.Proof R)} {batch : WorkerBatch Setup R}
    (result : Effects proofs batch) (token : Token) : ¬ Step proofs batch token token := by
  intro edge
  exact (lt_irrefl _) (result.steps token token edge)

theorem two_cycle_rejected {Setup R : Type} [Field R]
    {proofs : List (Airbender.NativeInitializationBatch.Proof R)} {batch : WorkerBatch Setup R}
    (result : Effects proofs batch) {a b : Token} (first : Step proofs batch a b) : ¬ Step proofs batch b a := by
  intro second
  have lower := result.steps a b first
  have upper := result.steps b a second
  omega

theorem three_cycle_rejected {Setup R : Type} [Field R]
    {proofs : List (Airbender.NativeInitializationBatch.Proof R)} {batch : WorkerBatch Setup R}
    (result : Effects proofs batch) {a b c : Token} (first : Step proofs batch a b) (second : Step proofs batch b c) :
    ¬ Step proofs batch c a := by
  intro third
  have ab := result.steps a b first
  have bc := result.steps b c second
  have ca := result.steps c a third
  omega

theorem any_finite_cycle_rejected {Setup R : Type} [Field R]
    {proofs : List (Airbender.NativeInitializationBatch.Proof R)} {batch : WorkerBatch Setup R}
    (result : Effects proofs batch) : NoCycles proofs batch := result.cycles

theorem complete_conditional {Setup R : Type} [Field R]
    (embed : F →+* R) (memory : MemoryKeyChallenges R) (ch : CSRArgumentChallenges R)
    (pc : PCChallenges R) (gamma : R) (config : WorkerConfiguration Setup)
    {proofs : List (Airbender.NativeInitializationBatch.Proof R)} {workers : WorkerBatch Setup R}
    {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : Airbender.NativeInitializationBatch.Accepted embed memory ch pc gamma config proofs workers inputs inverse)
    (identity : Airbender.NativeDelegationSupport.SourceIdentity proofs workers) : Effects proofs workers :=
  native_mixed_memory_order embed memory ch pc gamma config accepted identity

theorem complete_conditional_counted {Setup R : Type} [Field R]
    (embed : F →+* R) (memory : MemoryKeyChallenges R) (ch : CSRArgumentChallenges R)
    (pc : PCChallenges R) (gamma : R) (config : WorkerConfiguration Setup)
    {batch : Airbender.NativeMainBatch.Batch R} {workers : WorkerBatch Setup R}
    {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : Airbender.NativeMainBatch.SourceAccepted embed memory ch pc gamma config batch workers inputs inverse)
    (identity : Airbender.NativeDelegationSupport.SourceIdentity batch.proofs workers) :
    Airbender.NativeMainBatch.Effects batch ∧ Effects batch.proofs workers :=
  native_counted_mixed_memory_order embed memory ch pc gamma config accepted identity
end Airbender.Tests.NativeMixedMemoryOrder
