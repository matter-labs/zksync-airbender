import GKRProtocol.LookupSourceNative.AddSubCached

namespace Tests.GKRLookupSource
open Airbender Airbender.Compiler
set_option warningAsError true
set_option maxRecDepth 32768

private def wrongBank : WireBank 1 :=
  ⟨fun _ => .BaseLayerWitness 0, fun _ => ⟨0, by decide⟩⟩

/-- An arbitrary projection cannot erase an actual base-column input. -/
theorem rejects_unretained_actual_column :
    wrongBank.check (.input (.BaseLayerWitness 1)) = false := by decide +kernel

theorem accepts_retained_actual_column :
    wrongBank.check (.input (.BaseLayerWitness 0)) = true := by decide +kernel

private noncomputable def original := LookupSourceNative.AddSubCached.native.genericQueries

/-- The expected bank includes the independently authored decoder query. -/
theorem retains_authored_decoder_mask :
    ((original[original.length - 1]?).map (fun query => query.mask.isSome)).getD false = true := by
  decide +kernel

theorem rejects_omitted_decoder_occurrence :
    decide (List.Perm
      ((List.range (original.length + 1)).filter (fun index => index != original.length - 1))
      (List.range (original.length + 1))) = false := by decide +kernel

theorem rejects_query_replaced_by_setup :
    decide (List.Perm
      (((List.range original.length).map (fun index => if index == original.length - 1 then original.length else index)) ++
        [original.length])
      (List.range (original.length + 1))) = false := by decide +kernel

end Tests.GKRLookupSource
