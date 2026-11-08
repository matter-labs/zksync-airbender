import Airbender.Review.Circuits.ReducedMachine.StageTwoKeysTheorems
import Tests.NativeBlake2MemoryKeys

namespace Airbender.Tests.NativeStageTwoKeys
open Airbender.NativeStageTwoKeys
open Airbender.Blake2Worker.Native Airbender.ReducedMachine.Native Airbender.ReducedMachine.NativeMemoryBoundary
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

/-- Exact ABI syntax, sampled before witness data. -/
theorem zero_offset_bases : (keyDescriptor (1 : Fin 43)).location = .indirect #v[2,3] 0 ∧
    (keyDescriptor (26 : Fin 43)).location = .indirect #v[100,101] 0 :=
  Airbender.NativeStageTwoKeyProofs.base_locations

/-- Pure helper controls, not complete accepted native/physical rows. -/
theorem no_carry_endpoint : stageTwoIndirectAddress 65532 65535 3 = some ⟨0,65535,65535⟩ := by
  exact Airbender.NativeStageTwoKeyProofs.indirect_address (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem no_carry_zero : stageTwoIndirectAddress 0 0 0 = some ⟨0,0,0⟩ := by
  exact Airbender.NativeStageTwoKeyProofs.indirect_address (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem carry_reference : stageTwoIndirectAddress 65535 0 4 = some ⟨0,3,1⟩ :=
  Airbender.Tests.NativeBlake2MemoryKeys.stage_two_carry_boundary

theorem high_overflow_reference : stageTwoIndirectAddress 65535 65535 4 = none :=
  Airbender.Tests.NativeBlake2MemoryKeys.stage_two_high_overflow

private def widePointer (column : Nat) : F := if column = 2 then 65536 else 0

theorem wide_reference_difference :
    stageTwoKeyAddress widePointer (.indirect #v[2,3] 4) = some ⟨0,4,0⟩ ∧
    quotientKeyAddress widePointer (.indirect #v[2,3] 4) = ⟨0,65540,0⟩ := by decide +kernel

theorem carry_raw_domain_rejected : ¬ Airbender.NativeAddressSupport.Domain ⟨0,65539,0⟩ := by
  unfold Airbender.NativeAddressSupport.Domain
  decide +kernel

theorem wide_raw_domain_rejected : ¬ Airbender.NativeAddressSupport.Domain ⟨0,65536,0⟩ := by
  unfold Airbender.NativeAddressSupport.Domain
  decide +kernel

theorem zero_factor_stays : memoryKeyArgument (RingHom.id F) ⟨0,0,0,0,0,0,0⟩
    ⟨⟨0,4,0⟩,#v[0,0],#v[0,0]⟩ = 0 := by decide +kernel

theorem all_positions (w : Nat → F) (write : Bool) :
    (Airbender.NativeMemoryTokens.workerTokens w write).length = 43 :=
  Airbender.NativeMemoryTokenProofs.worker_count w write

theorem actual_base_reads {Setup R : Type} [Field R]
    {proofs : List (Airbender.NativeInitializationBatch.Proof R)} {batch : WorkerBatch Setup R} {inputs : PublicBoundary}
    (result : Effects proofs batch inputs) {w : Nat → F} (member : w ∈ Airbender.NativeTokenLedger.workerRows batch)
    (active : w constraintsABI.multiplicity = 1) :
    (w 2).val < 65536 ∧ (w 3).val < 65536 ∧ (w 100).val < 65536 ∧ (w 101).val < 65536 :=
  Airbender.NativeStageTwoKeyProofs.base_bounds (result.addresses.workers w member active)

theorem actual_read_keys {Setup R : Type} [Field R]
    {proofs : List (Airbender.NativeInitializationBatch.Proof R)} {batch : WorkerBatch Setup R} {inputs : PublicBoundary}
    (result : Effects proofs batch inputs) {w : Nat → F} (member : w ∈ Airbender.NativeTokenLedger.workerRows batch) (slot : Fin 43) :
    stageTwoMemoryKey w slot false = some (quotientMemoryKey w slot false) := result.keys w member slot false

theorem actual_write_keys {Setup R : Type} [Field R]
    {proofs : List (Airbender.NativeInitializationBatch.Proof R)} {batch : WorkerBatch Setup R} {inputs : PublicBoundary}
    (result : Effects proofs batch inputs) {w : Nat → F} (member : w ∈ Airbender.NativeTokenLedger.workerRows batch) (slot : Fin 43) :
    stageTwoMemoryKey w slot true = some (quotientMemoryKey w slot true) := result.keys w member slot true

theorem no_helper_failure {Setup R : Type} [Field R]
    {proofs : List (Airbender.NativeInitializationBatch.Proof R)} {batch : WorkerBatch Setup R} {inputs : PublicBoundary}
    (result : Effects proofs batch inputs) {w : Nat → F} (member : w ∈ Airbender.NativeTokenLedger.workerRows batch)
    (slot : Fin 43) (write : Bool) : stageTwoMemoryKey w slot write ≠ none := by
  rw [result.keys w member slot write]
  exact Option.some_ne_none _

theorem complete_conditional {Setup R : Type} [Field R]
    (embed : F →+* R) (memory : MemoryKeyChallenges R) (ch : CSRArgumentChallenges R)
    (pc : PCChallenges R) (gamma : R) (config : WorkerConfiguration Setup)
    {proofs : List (Airbender.NativeInitializationBatch.Proof R)} {workers : WorkerBatch Setup R}
    {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : Airbender.NativeInitializationBatch.Accepted embed memory ch pc gamma config proofs workers inputs inverse)
    (identity : Airbender.NativeDelegationSupport.SourceIdentity proofs workers) : Effects proofs workers inputs :=
  native_worker_stage_two_keys embed memory ch pc gamma config accepted identity

theorem complete_conditional_counted {Setup R : Type} [Field R]
    (embed : F →+* R) (memory : MemoryKeyChallenges R) (ch : CSRArgumentChallenges R)
    (pc : PCChallenges R) (gamma : R) (config : WorkerConfiguration Setup)
    {batch : Airbender.NativeMainBatch.Batch R} {workers : WorkerBatch Setup R}
    {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : Airbender.NativeMainBatch.SourceAccepted embed memory ch pc gamma config batch workers inputs inverse)
    (identity : Airbender.NativeDelegationSupport.SourceIdentity batch.proofs workers) :
    Airbender.NativeMainBatch.Effects batch ∧ Effects batch.proofs workers inputs :=
  native_counted_worker_stage_two_keys embed memory ch pc gamma config accepted identity

end Airbender.Tests.NativeStageTwoKeys
