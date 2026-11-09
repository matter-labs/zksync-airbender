import Airbender.Proofs.Memory.FiniteLedger
import Airbender.Proofs.ReducedMachine.PointerPrefix.LedgerSteps
import Airbender.Review.Trace.Families.ReducedMachine.PointerLedger
import Airbender.Proofs.ReducedMachine.NativePointerPrefix

namespace Airbender.NativePointerLedgerProofs
open Airbender.NativePointerLedger Airbender.NativeMemoryTokens
open Airbender.ReducedMachine.NativeMainAuxiliary
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

theorem memory_balanced : MemoryBalanced NativePointerPrefixProofs.assignment := by
  have complete := PrefixLedgerProofs.finite_fold 41 registerState
    (fun row => mainTokens (NativePointerPrefixProofs.assignment row) true)
    (fun row => mainTokens (NativePointerPrefixProofs.assignment row) false) gpr_step
  simpa only [MemoryBalanced,rowsList,List.flatMap_map,initial_registers,final_registers] using complete

theorem pc_balanced : PCBalanced NativePointerPrefixProofs.assignment := by
  have complete := PrefixLedgerProofs.finite_fold 41 (fun i => [pcState i])
    (fun row => [mainPCKey (NativePointerPrefixProofs.assignment row) true])
    (fun row => [mainPCKey (NativePointerPrefixProofs.assignment row) false]) pc_step
  simpa only [PCBalanced,rowsList,List.map_map,Function.comp_def,List.singleton_append,
    ← List.map_eq_flatMap,initial_pc,final_pc] using complete

theorem balanced : Balanced NativePointerPrefixProofs.assignment :=
  ⟨memory_balanced,pc_balanced⟩

theorem fixture : ∃ activeRows idle, NativePointerPrefix.Components activeRows idle ∧ Balanced activeRows :=
  ⟨NativePointerPrefixProofs.assignment,NativeSparseMainProofs.idle,
    NativePointerPrefixProofs.components,balanced⟩
end Airbender.NativePointerLedgerProofs
