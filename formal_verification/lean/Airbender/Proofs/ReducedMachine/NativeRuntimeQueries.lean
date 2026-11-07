import Airbender.Review.Circuits.ReducedMachine.NativeArtifact
import Airbender.Review.Circuits.ReducedMachine.Tables.RuntimePoolTheorems
import Airbender.Proofs.Constraints
import Airbender.Review.Helpers.Properties
import Mathlib.Tactic.FinCases

namespace Airbender.ReducedMachine.NativeRuntimeQueryProofs
open Verification
set_option warningAsError true
set_option Elab.async false

/-- Extract the two actual constant queries from original Clean acceptance. -/
theorem queries {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w)
      (Native.importedConstraints NativeRuntimePool.table)) :
    (NativeRuntimePool.table (p := mersenne31Modulus)).Contains #[] #v[w 36,w 56,w 57,16] ∧
      (NativeRuntimePool.table (p := mersenne31Modulus)).Contains #[] #v[w 48,w 59,w 60,16] := by
  constructor
  · have query := lookup_of_holds holds ⟨16,by change 16 < 22; decide⟩
    simpa [Native.importedConstraints,FlatOperation.lookups,Lookup.Contains,
      Table.toRaw,NativeRuntimePool.table,Table.fromStatic,StaticTable.toTable,
      Expression.eval,environment,ProvableType.fromElements] using query
  · have query := lookup_of_holds holds ⟨17,by change 17 < 22; decide⟩
    simpa [Native.importedConstraints,FlatOperation.lookups,Lookup.Contains,
      Table.toRaw,NativeRuntimePool.table,Table.fromStatic,StaticTable.toTable,
      Expression.eval,environment,ProvableType.fromElements] using query

theorem results {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w)
      (Native.importedConstraints NativeRuntimePool.table)) :
    (w 36).val < 65536 ∧ (w 56).val = (w 36).val / 32768 ∧
      (w 57).val = (w 36).val / 256 ∧
    (w 48).val < 65536 ∧ (w 59).val = (w 48).val / 32768 ∧
      (w 60).val = (w 48).val / 256 := by
  obtain ⟨first,second⟩ := queries holds
  have a := NativeRuntimePool.sign_high _ first rfl
  have b := NativeRuntimePool.sign_high _ second rfl
  exact ⟨a.1,a.2.1,a.2.2.1,b.1,b.2.1,b.2.2.1⟩

/-- All four actual dynamic selectors remain evaluated fourth query fields. -/
theorem dynamic_queries {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w)
      (Native.importedConstraints NativeRuntimePool.table)) (slot : Fin 4) :
    (NativeRuntimePool.table (p := mersenne31Modulus)).Contains #[]
      #v[w (100 + 4 * slot.val),w (101 + 4 * slot.val),
        w (102 + 4 * slot.val),w (103 + 4 * slot.val)] := by
  fin_cases slot
  · have query := lookup_of_holds holds ⟨18,by change 18 < 22; decide⟩
    simpa [Native.importedConstraints,FlatOperation.lookups,Lookup.Contains,
      Table.toRaw,NativeRuntimePool.table,Table.fromStatic,StaticTable.toTable,
      Expression.eval,environment,ProvableType.fromElements] using query
  · have query := lookup_of_holds holds ⟨19,by change 19 < 22; decide⟩
    simpa [Native.importedConstraints,FlatOperation.lookups,Lookup.Contains,
      Table.toRaw,NativeRuntimePool.table,Table.fromStatic,StaticTable.toTable,
      Expression.eval,environment,ProvableType.fromElements] using query
  · have query := lookup_of_holds holds ⟨20,by change 20 < 22; decide⟩
    simpa [Native.importedConstraints,FlatOperation.lookups,Lookup.Contains,
      Table.toRaw,NativeRuntimePool.table,Table.fromStatic,StaticTable.toTable,
      Expression.eval,environment,ProvableType.fromElements] using query
  · have query := lookup_of_holds holds ⟨21,by change 21 < 22; decide⟩
    simpa [Native.importedConstraints,FlatOperation.lookups,Lookup.Contains,
      Table.toRaw,NativeRuntimePool.table,Table.fromStatic,StaticTable.toTable,
      Expression.eval,environment,ProvableType.fromElements] using query

/-- Native acceptance derives selector domains, without per-row selector premises. -/
theorem dynamic_selectors {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w)
      (Native.importedConstraints NativeRuntimePool.table)) (slot : Fin 4) :
    (w (103 + 4 * slot.val)).val ∈ NativeRuntimePool.tags :=
  NativeRuntimePoolProofs.accepted_selector _ (dynamic_queries holds slot)

end Airbender.ReducedMachine.NativeRuntimeQueryProofs
