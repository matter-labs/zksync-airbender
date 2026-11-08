import Airbender.Review.Circuits.ReducedMachine.AddressSupportTheorems

namespace Airbender.Tests.NativeAddressSupport
open Airbender.NativeAddressSupport
open Airbender.Blake2Worker.Native Airbender.ReducedMachine.Native Airbender.ReducedMachine.NativeMemoryBoundary
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

/-- Pure canonical-address controls, not accepted native/physical witnesses. -/
theorem register_zero : Domain (cellAddress (.register 0)) :=
  (Airbender.NativeAddressSupportProofs.cell_address _).2

theorem register_max : cellAddress (.register 31) = ⟨1,31,0⟩ ∧ Domain ⟨1,31,0⟩ := by
  constructor
  · rfl
  · exact (Airbender.NativeAddressSupportProofs.cell_address (.register 31)).2

theorem ram_max : cellAddress (.ram 4294967295) = ⟨0,65535,65535⟩ ∧ Domain ⟨0,65535,65535⟩ := by
  constructor
  · decide +kernel
  · exact (Airbender.NativeAddressSupportProofs.cell_address (.ram 4294967295)).2

theorem ram_above_field : cellAddress (.ram 2147483648) = ⟨0,0,32768⟩ ∧ Domain ⟨0,0,32768⟩ := by
  constructor
  · decide +kernel
  · exact (Airbender.NativeAddressSupportProofs.cell_address (.ram 2147483648)).2

theorem wide_limb_rejected : ¬ Domain ⟨0,65536,0⟩ := by unfold Domain; decide +kernel

theorem nonboolean_space_rejected : ¬ Domain ⟨2,0,0⟩ := by unfold Domain; decide +kernel

theorem register32_rejected : ¬ Domain ⟨1,32,0⟩ := by unfold Domain; decide +kernel

theorem address_sentinel_rejected : ¬ Domain ⟨0,-1,0⟩ := by unfold Domain; decide +kernel

theorem spaces_distinct : Airbender.NativeMemoryTokens.encodeAddress ⟨1,0,0⟩ ≠
    Airbender.NativeMemoryTokens.encodeAddress ⟨0,0,0⟩ := by decide +kernel

theorem actual_edge_preserves_address {Setup R : Type} [Field R]
    {proofs : List (Airbender.NativeInitializationBatch.Proof R)} {batch : WorkerBatch Setup R}
    {read write : Token} (edge : Airbender.NativeMixedMemoryOrder.Step proofs batch read write) :
    read.address = write.address := Airbender.NativeAddressSupportProofs.step_address edge

theorem actual_read_cell {Setup R : Type} [Field R]
    {proofs : List (Airbender.NativeInitializationBatch.Proof R)} {batch : WorkerBatch Setup R} {inputs : PublicBoundary}
    (result : Effects proofs batch inputs) {read write : Token}
    (edge : Airbender.NativeMixedMemoryOrder.Step proofs batch read write) :
    ∃ cell ∈ Airbender.NativeInitializationSeedBoundary.cells proofs, read.address = cell.addressCode := by
  obtain ⟨cell,present,read,_⟩ := result.cells read write edge
  exact ⟨cell,present,read⟩

theorem actual_write_cell {Setup R : Type} [Field R]
    {proofs : List (Airbender.NativeInitializationBatch.Proof R)} {batch : WorkerBatch Setup R} {inputs : PublicBoundary}
    (result : Effects proofs batch inputs) {read write : Token}
    (edge : Airbender.NativeMixedMemoryOrder.Step proofs batch read write) :
    ∃ cell ∈ Airbender.NativeInitializationSeedBoundary.cells proofs, write.address = cell.addressCode := by
  obtain ⟨cell,present,_,write⟩ := result.cells read write edge
  exact ⟨cell,present,write⟩

theorem actual_worker_address_limbs {Setup R : Type} [Field R]
    {proofs : List (Airbender.NativeInitializationBatch.Proof R)} {batch : WorkerBatch Setup R} {inputs : PublicBoundary}
    (result : Effects proofs batch inputs) {w : Nat → F} (member : w ∈ Airbender.NativeTokenLedger.workerRows batch)
    (active : w constraintsABI.multiplicity = 1) (slot : Fin 43) :
    (quotientMemoryKey w slot false).address.low.val < 65536 ∧
      (quotientMemoryKey w slot false).address.high.val < 65536 := by
  rcases result.workers w member active slot with ⟨_,low,high⟩ | ⟨_,low,high⟩
  · exact ⟨by omega,by rw [high]; decide +kernel⟩
  · exact ⟨low,high⟩

theorem inactive_read_stays {Setup R : Type} [Field R]
    (proofs : List (Airbender.NativeInitializationBatch.Proof R)) {batch : WorkerBatch Setup R}
    {w : Nat → F} (member : w ∈ Airbender.NativeTokenLedger.workerRows batch)
    (zero : w constraintsABI.multiplicity = 0) (slot : Fin 43) :
    w constraintsABI.multiplicity = 0 ∧ Airbender.NativeWorkerClockProgress.readToken w slot ∈
      Airbender.NativeInitializationSeedBoundary.accessTokens proofs batch false :=
  ⟨zero,Airbender.NativeWorkerClockProgressProofs.read_member proofs member slot⟩

theorem complete_conditional {Setup R : Type} [Field R]
    (embed : F →+* R) (memory : MemoryKeyChallenges R) (ch : CSRArgumentChallenges R)
    (pc : PCChallenges R) (gamma : R) (config : WorkerConfiguration Setup)
    {proofs : List (Airbender.NativeInitializationBatch.Proof R)} {workers : WorkerBatch Setup R}
    {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : Airbender.NativeInitializationBatch.Accepted embed memory ch pc gamma config proofs workers inputs inverse)
    (identity : Airbender.NativeDelegationSupport.SourceIdentity proofs workers) : Effects proofs workers inputs :=
  native_memory_address_support embed memory ch pc gamma config accepted identity

theorem complete_conditional_counted {Setup R : Type} [Field R]
    (embed : F →+* R) (memory : MemoryKeyChallenges R) (ch : CSRArgumentChallenges R)
    (pc : PCChallenges R) (gamma : R) (config : WorkerConfiguration Setup)
    {batch : Airbender.NativeMainBatch.Batch R} {workers : WorkerBatch Setup R}
    {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : Airbender.NativeMainBatch.SourceAccepted embed memory ch pc gamma config batch workers inputs inverse)
    (identity : Airbender.NativeDelegationSupport.SourceIdentity batch.proofs workers) :
    Airbender.NativeMainBatch.Effects batch ∧ Effects batch.proofs workers inputs :=
  native_counted_memory_address_support embed memory ch pc gamma config accepted identity

end Airbender.Tests.NativeAddressSupport
