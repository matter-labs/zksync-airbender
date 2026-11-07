import Airbender.Review.Circuits.ReducedMachine.TokenLedgerTheorems
import Airbender.Proofs.ReducedMachine.NativeCSRPositiveWitness

namespace Airbender.Tests.NativeTokenLedger
open Airbender.NativeTokenLedger Airbender.NativeTokenLedgerProofs Airbender.NativeMemoryTokens
open Airbender.ReducedMachine.NativeMainAuxiliary Airbender.ReducedMachine.NativeMemoryBoundary
open Airbender.Blake2Worker.Native
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

theorem complete_native_domains :
    Airbender.ReducedMachine.Native.callerAuxiliaryLayout.traceLength-1 = 8388607 ∧
    constraintsABI.traceLength-1 = 1048575 := by decide +kernel

theorem four_port_state_tokens (w : Nat → F) (write : Bool) : (portTokens w write).length = 4 := by
  simp only [portTokens,List.length_append,List.length_map,List.length_singleton]
  rw [← NativeMemoryTokenProofs.main_list]
  simp

theorem five_row_tokens (w : Nat → F) (write : Bool) : (rowTokens w write).length = 5 := by
  simp [rowTokens,four_port_state_tokens]

theorem all_worker_accesses (w : Nat → F) (write : Bool) : (workerRowTokens w write).length = 43 := by
  simp [workerRowTokens,NativeMemoryTokenProofs.worker_count]

theorem public_registers_and_pc (inputs : PublicBoundary) (write : Bool) :
    (publicTokens inputs write).length = 33 := by simp [publicTokens]

theorem inactive_uses_incoming (w : Nat → F)
    (inactive : w Airbender.ReducedMachine.Native.importedConstraintsTraceColumns.execute = 0) :
    rowTokens w true = [Token.memory (encodeKey (initializationKey w true))] ++ portTokens w false ∧
    rowTokens w false = [Token.memory (encodeKey (initializationKey w false))] ++ portTokens w false := by
  simp [rowTokens,inactive]

theorem active_uses_outgoing (w : Nat → F)
    (active : w Airbender.ReducedMachine.Native.importedConstraintsTraceColumns.execute = 1) :
    rowTokens w true = [Token.memory (encodeKey (initializationKey w true))] ++ portTokens w true := by
  simp [rowTokens,active]

private def initializationWitness (column : Nat) : F :=
  if column = 126 then 17 else if column = 128 then 9 else if column = 130 then 7 else 0

/-- This is a raw token observation, not an accepted initialization row. -/
theorem inactive_initialization_not_filtered :
    activeRowTokens initializationWitness true = [Token.memory (encodeKey (initializationKey initializationWitness true))] ∧
    (decodeKey (encodeKey (initializationKey initializationWitness false))).value = #v[9,0] ∧
    (decodeKey (encodeKey (initializationKey initializationWitness false))).time = #v[7,0] := by
  constructor
  · decide +kernel
  · rw [NativeMemoryTokenProofs.decode_encode]
    exact ⟨by decide +kernel,by decide +kernel⟩

/-- Reuses the complete native BODY witness. Filtering memory/state contribution
    does not erase its request1. It is NOT full auxiliary/global acceptance. -/
theorem inactive_csr_request_retained :
    FlatOperation.ConstraintsHoldFlat
      (Verification.environment (Airbender.ReducedMachine.NativeCSRPositiveWitness.assignment false))
      (Airbender.ReducedMachine.Native.importedConstraints Airbender.ReducedMachine.NativeRuntimePool.table) ∧
    Airbender.ReducedMachine.NativeCSRPositiveWitness.assignment false 92 = 1 ∧
    (inactiveRowTokens (Airbender.ReducedMachine.NativeCSRPositiveWitness.assignment false)).length = 4 := by
  refine ⟨Airbender.ReducedMachine.NativeCSRPositiveWitness.body false,by decide +kernel,?_⟩
  have inactive : Airbender.ReducedMachine.NativeCSRPositiveWitness.assignment false
      Airbender.ReducedMachine.Native.importedConstraintsTraceColumns.execute ≠ 1 := by decide +kernel
  simp [inactiveRowTokens,inactive,four_port_state_tokens]

theorem identical_duplicates_cancel (a b : Token) :
    ([a,a]++[b,b]).Perm ([a]++[b,b]) ↔ ([a,a] : List Token).Perm [a] := by
  constructor
  · intro h
    have equality := Multiset.coe_eq_coe.mpr h
    apply Multiset.coe_eq_coe.mp
    simpa only [← Multiset.coe_add,add_right_cancel_iff] using equality
  · intro h
    exact h.append_right _

private def zeroMemory : MemoryKeyChallenges F := ⟨0,0,0,0,0,0,0⟩
private def zeroPC : PCChallenges F := ⟨0,0,0,0⟩

/-- An inactive row's incoming factors remain even when their compression is
    zero. No ratio1 or factor cancellation is used by the logical filter. -/
theorem zero_factors_still_have_tokens :
    (rowTokens (fun _ => 0) false).length = 5 ∧
    ((rowTokens (fun _ => 0) false).map (argument (RingHom.id F) zeroMemory zeroPC)).prod = 0 := by
  exact ⟨five_row_tokens _ _,by decide +kernel⟩

theorem complete_conditional_matching {Setup R : Type} [Field R] (mains : List (MainProof R))
    (batch : WorkerBatch Setup R) (inputs : PublicBoundary) :
    LogicalMatching mains batch inputs ↔
      (activeTokens mains batch inputs true).Perm (activeTokens mains batch inputs false) :=
  native_logical_active_matching mains batch inputs

end Airbender.Tests.NativeTokenLedger
