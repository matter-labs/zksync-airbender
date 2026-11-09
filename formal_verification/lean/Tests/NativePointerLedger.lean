import Airbender.Review.Trace.Families.ReducedMachine.PointerLedgerTheorems

namespace Airbender.Tests.NativePointerLedger
open Airbender.NativePointerLedger Airbender.NativePointerLedgerProofs
open Airbender.NativeMemoryTokens Airbender.ReducedMachine.NativeMainAuxiliary
open Airbender.ReducedMachine.NativeMemoryBoundary Airbender.Blake2Worker.Native
set_option autoImplicit false
set_option warningAsError true

-- Finite prefix components/reference controls; no whole accepted worker,
-- physical verifier, fetched original program or global SourceAccepted claim.
theorem positions : (rowsList NativePointerPrefixProofs.assignment).length = 41 := by
  simp [rowsList]

theorem writes_count : ((rowsList NativePointerPrefixProofs.assignment).flatMap
    (fun w => mainTokens w true)).length = 123 := by decide +kernel

theorem reads_count : ((rowsList NativePointerPrefixProofs.assignment).flatMap
    (fun w => mainTokens w false)).length = 123 := by decide +kernel

theorem all_gpr_seeds : NativeInitializationSeedBoundary.initialRegisters.length = 32 := by decide +kernel

theorem all_gpr_endpoints :
    (NativeInitializationSeedBoundary.finalRegisters NativePointerPrefix.prefixEndpoint).length = 32 := by decide +kernel

theorem pc_count : (initialPCKey :: (rowsList NativePointerPrefixProofs.assignment).map
    (fun w => mainPCKey w true)).length = 42 := by simp [rowsList]

theorem x0_final : (NativePointerPrefix.prefixEndpoint.registers 0).value = 0 ∧
    (NativePointerPrefix.prefixEndpoint.registers 0).time = #v[166,0] := by decide +kernel

theorem x10_final : (NativePointerPrefix.prefixEndpoint.registers 10).value = 0 ∧
    (NativePointerPrefix.prefixEndpoint.registers 10).time = #v[0,0] := by decide +kernel

theorem x11_final : (NativePointerPrefix.prefixEndpoint.registers 11).value = 128 ∧
    (NativePointerPrefix.prefixEndpoint.registers 11).time = #v[162,0] := by decide +kernel

theorem before_csr : (registerStateKey 40 11).value = #v[128,0] ∧
    (registerStateKey 40 11).time = #v[162,0] ∧
    (registerStateKey 40 0).time = #v[161,0] := by decide +kernel

theorem retained_high_time : encodeKey (registerStateKey 41 11) ≠
    encodeKey ⟨(registerStateKey 41 11).address,(registerStateKey 41 11).value,#v[162,1]⟩ := by decide +kernel

theorem readonly_refresh_changes_token :
    encodeKey (mainMemoryKey (NativePointerPrefixProofs.assignment 0) 0 true) ≠
      encodeKey (mainMemoryKey (NativePointerPrefixProofs.assignment 0) 0 false) := by decide +kernel

theorem first_ledger_step :
    (registerState 0 ++ mainTokens (NativePointerPrefixProofs.assignment 0) true).Perm
      (registerState 1 ++ mainTokens (NativePointerPrefixProofs.assignment 0) false) := gpr_step 0

theorem last_ledger_step :
    (registerState 40 ++ mainTokens (NativePointerPrefixProofs.assignment 40) true).Perm
      (registerState 41 ++ mainTokens (NativePointerPrefixProofs.assignment 40) false) := gpr_step 40

theorem final_pc_observation : finalPCKey NativePointerPrefix.prefixEndpoint = pcState 41 := final_pc.symm

theorem wrong_pc_time_rejected :
    ¬ ([initialPCKey,mainPCKey (NativePointerPrefixProofs.assignment 0) true]).Perm
      ([⟨#v[4,0],#v[9,0]⟩,mainPCKey (NativePointerPrefixProofs.assignment 0) false]) := by decide +kernel

theorem duplicate_positions : (([0,0] : List (Fin 41)).map NativePointerPrefixProofs.assignment).length = 2 := by rfl

theorem duplicated_ports : (([0,0] : List (Fin 41)).flatMap
    (fun row => mainTokens (NativePointerPrefixProofs.assignment row) true)).length = 6 := by decide +kernel

theorem complete_memory : MemoryBalanced NativePointerPrefixProofs.assignment := memory_balanced

theorem complete_pc : PCBalanced NativePointerPrefixProofs.assignment := pc_balanced

theorem same_full_components : ∃ activeRows idle,
    NativePointerPrefix.Components activeRows idle ∧ Balanced activeRows := fixture
end Airbender.Tests.NativePointerLedger
