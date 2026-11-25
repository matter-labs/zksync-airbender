module
public import Human.Trace.UnifiedReduced.Proth120Padding
public import Proven.Final.Trace.UnifiedReduced.Proth120NativeTrace
public import Proven.Trace.PaddingBoundary

@[expose] public section
namespace Airbender.UnifiedReduced.Proth120
open Trace Compiler.NativeMemory PaddingBoundary PaddingBoundary.Proofs

/-- At every physical row, symbolic token masking agrees with the native scalar gate for
    every encoding. The native constraints enforce the Boolean selector even on disabled rows. -/
theorem PaddedInputs.mask_eq {t initial cells} (h : PaddedInputs t initial cells) {r} (mem : r ∈ t.rows)
    (encode : MemoryToken proth120Modulus → F) (token : MemoryToken proth120Modulus) :
    evaluate encode (contribution (r.assignment r.columns.execute) token) =
      mask (r.assignment r.columns.execute) (encode token) := by
  obtain ⟨rows, physical, arith, matched⟩ := (h.rows r mem).2
  have full := (native_row _ _ rows physical _ arith matched).1
  have core := Verification.holds_of_sublist full (List.sublist_append_left _ importedConstraintsTimestampLookups)
  exact evaluate_contribution _ (UnifiedReduced.Standard.Proofs.local_flags (profile := .proth120) (Standard.holds core) 0) _ _

theorem PaddedInputs.project {t initial cells} (h : PaddedInputs t initial cells) :
    NativeTraceInputs (active t) initial cells := by
  refine ⟨h.toTraceBoundary, ?_, ?_⟩
  · have matched := h.permutation.filterMap (fun value => value)
    simpa only [maskedTokens, List.filterMap_cons, List.filterMap_append, List.filterMap_map,
      Function.comp_def, List.filterMap_some, erase_contributions, flatMap_values, WrapPermutation,
      active, List.map_cons, List.map_map, List.cons_append] using matched
  · intro row mem
    have selected : row.assignment row.columns.execute = 1 := of_decide_eq_true (List.mem_filter.mp mem).2
    obtain ⟨range, cert⟩ := h.rows row (List.mem_of_mem_filter mem)
    exact ⟨(range selected).1, (range selected).2, selected, cert⟩

end Airbender.UnifiedReduced.Proth120
