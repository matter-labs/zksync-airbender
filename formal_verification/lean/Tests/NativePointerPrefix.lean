import Airbender.Review.Trace.Families.ReducedMachine.PointerPrefixTheorems

namespace Airbender.Tests.NativePointerPrefix
open Airbender.NativePointerPrefixProofs Airbender.NativePointerPrefix
open Airbender.Verification Airbender.ReducedMachine Airbender.ReducedMachine.Native
open Airbender.ReducedMachine.NativeMainAuxiliary Airbender.Blake2Worker.Native
set_option autoImplicit false
set_option warningAsError true

-- Finite native/reference component controls, not whole accepted workers,
-- authenticated program execution, global matching or physical proof witnesses.
theorem geometry : blockStart = 8388566 ∧ callerAuxiliaryLayout.traceLength - 2 = 8388606 := by decide +kernel

theorem first_active : assignment 0 importedConstraintsTraceColumns.execute = 1 := active_fields 0

theorem first_write : (mainMemoryKey (assignment 0) 2 true).address = ⟨1,11,0⟩ ∧
    (mainMemoryKey (assignment 0) 2 true).value = #v[128,0] ∧
    (mainMemoryKey (assignment 0) 2 true).time = #v[6,0] := first_pointer_write

theorem last_pointer_read : (mainMemoryKey (assignment 39) 2 false).value = #v[128,0] ∧
    (mainMemoryKey (assignment 39) 2 false).time = #v[158,0] := by decide +kernel

theorem last_pointer_write : (mainMemoryKey (assignment 39) 2 true).value = #v[128,0] ∧
    (mainMemoryKey (assignment 39) 2 true).time = #v[162,0] := by decide +kernel

theorem first_x0_old : (mainMemoryKey (assignment 0) 0 false).time = #v[0,0] ∧
    (mainMemoryKey (assignment 0) 1 false).time = #v[4,0] := by decide +kernel

theorem csr_x0_old : (mainMemoryKey (assignment 40) 0 false).time = #v[161,0] ∧
    (mainMemoryKey (assignment 40) 1 false).time = #v[164,0] ∧
    (mainMemoryKey (assignment 40) 2 false).time = #v[165,0] := by decide +kernel

theorem actual_caller : csrRequest (assignment 40) = ⟨1,1991,some 0,3⟩ ∧
    NativeDelegationSupport.callerKey (assignment 40) = ⟨1991,0,167,0⟩ := caller_fields

theorem pointer_not_caller : (csrRequest (assignment 0)).multiplicity = 0 := by decide +kernel

theorem first_pc : (mainPCKey (assignment 0) false).pc = #v[0,0] ∧
    (mainPCKey (assignment 0) false).time = #v[4,0] := by decide +kernel

theorem final_pc : (mainPCKey (assignment 40) true).pc = #v[164,0] ∧
    (mainPCKey (assignment 40) true).time = #v[168,0] := by decide +kernel

theorem ram_zero_nonpadding : NativeInitializationBoundary.record (assignment 1) = #v[0,0,0,0,167,0] ∧
    NativeInitializationLedger.paddingRow (assignment 1) = false := by constructor <;> decide +kernel

theorem state_last : NativeInitializationBoundary.record (assignment 24) = #v[92,0,0,0,167,0] := by decide +kernel

theorem message_first : NativeInitializationBoundary.record (assignment 25) = #v[128,0,0,0,167,0] := by decide +kernel

theorem message_last : NativeInitializationBoundary.record (assignment 40) = #v[188,0,0,0,167,0] := by decide +kernel

theorem gap_remainder : (NativeInitializationOrdering.remainder (assignment 24))[0] = 65500 := by decide +kernel

theorem reversed_order_rejected : ¬ NativeInitializationOrdering.AdjacentAccepted (assignment 25) (assignment 24) := by
  intro accepted
  have wrong := accepted.low
  exact (by decide +kernel : NativeInitializationOrdering.lowTerm (1 : Airbender.NativePointerPrefix.F)
    (NativeInitializationOrdering.address (assignment 25))[0]
    (NativeInitializationOrdering.address (assignment 24))[0]
    (NativeInitializationOrdering.remainder (assignment 25))[0]
    (NativeInitializationOrdering.borrows (assignment 25))[0] ≠ 0) wrong

theorem wrong_endpoint_time_rejected : ¬ NativeInitializationBoundary.EndpointAccepted
    (assignment 40) #v[188,0,0,0,168,0] := by
  intro accepted
  exact (by decide +kernel : NativeInitializationBoundary.term (1 : Airbender.NativePointerPrefix.F)
    (NativeInitializationBoundary.record (assignment 40))[4] (168 : Airbender.NativePointerPrefix.F) ≠ 0) (accepted 4)

theorem all_actual_body : ∀ row : Fin 41,
    FlatOperation.ConstraintsHoldFlat (environment (assignment row)) (importedConstraints NativeRuntimePool.table) := body

theorem all_ordinary_ordering : ∀ i < callerAuxiliaryLayout.traceLength - 2,
    NativeInitializationOrdering.AdjacentAccepted (rows i) (rows (i + 1)) := ordinary_adjacent

theorem all_public_fields : NativeInitializationBoundary.EndpointAccepted (rows 0) endpoints.first ∧
    NativeInitializationBoundary.EndpointAccepted (rows (callerAuxiliaryLayout.traceLength - 2)) endpoints.oneBeforeLast := public_endpoints

theorem full_components : Components assignment NativeSparseMainProofs.idle := components
end Airbender.Tests.NativePointerPrefix
