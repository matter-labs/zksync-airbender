module
public import Proven.UnifiedReduced.Proth120.Padding

@[expose] public section
namespace Airbender.UnifiedReduced.Proth120.Witness
open Trace PaddingBoundary
set_option maxRecDepth 32768

/-- The disabled row still advances its local clock and satisfies the wide Montgomery equation. -/
def paddingAssignment : Nat → F
  | 2 | 30 => 4
  | 32 => 8
  | 78 => 2013265921
  | 123 | 124 | 125 => 1
  | _ => 0

abbrev paddingRow : Row proth120Modulus Kind := ⟨.machine, paddingAssignment⟩
noncomputable def padded : WrapTrace := { trace with rows := [paddingRow, row] }

private theorem certificate (r : Row proth120Modulus Kind) (pc : r.start.word.toBitVec = initial.pc)
    (read : isRead r = false)
    (arith : NativeArithmetic (physicalFor r.assignment) r.assignment)
    (matched : NativeLookupsMatched nativeRows.generic (physicalFor r.assignment)) : NativeRowEvidence padded initial r := by
  refine ⟨⟨nativeRows.generic, nativeRows.pooled, ?_⟩, _, arith, matched⟩
  intro v hv
  rw [pc]
  exact Or.inl ⟨read, nativeRows.decoder v hv⟩

theorem padded_inputs : PaddedInputs padded initial cells where
  toTraceBoundary := trace_inputs.toTraceBoundary
  permutation := by decide +kernel
  rows r mem := by
    rcases List.mem_cons.mp mem with rfl | mem
    · refine ⟨fun selected => False.elim ((by decide +kernel : paddingRow.assignment paddingRow.columns.execute ≠ 1) selected), ?_⟩
      exact certificate _ rfl rfl (arithmetic_of_checks _ (by kernel_rfl) (by kernel_rfl)) (matched_of_check _ (by kernel_rfl))
    · obtain rfl := List.mem_singleton.mp mem
      exact ⟨fun _ => fma_inputs.fetch, certificate _ rfl rfl nativeArithmetic nativeMatched⟩

end Airbender.UnifiedReduced.Proth120.Witness
