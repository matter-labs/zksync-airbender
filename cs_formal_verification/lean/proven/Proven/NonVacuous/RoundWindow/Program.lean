module
public import Proven.NonVacuous.RoundWindow.Rows

@[expose] public section
namespace Airbender.NonVacuous.RoundWindow
open Trace Trace.Machine HashCallers
set_option warningAsError true

/-- Production preprocessing reads all ten unrolled round callers from public ROM. -/
theorem unrolled_program_image : rvMachineProgramImage .unrolledFullUnsigned initial addresses =
    some unrolledProgram := by kernel_rfl

/-- Production preprocessing reads the same ten callers for the unified CPU. -/
theorem unified_program_image : rvMachineProgramImage .unified initial addresses =
    some unifiedProgram := by kernel_rfl

/-- Every unrolled query retains the complete public CSR decoder row. -/
theorem unrolled_query_check : (List.range 10).all (fun index => decide (
    (unrolledRow index).decoderQuery =
      ((entry (.pooled .addSub) (BitVec.ofNat 32 (4 * index))).data.row
        (BitVec.ofNat 32 (4 * index))).map (fun value : Nat => (value : ZMod babyBearModulus)))) = true := by
  kernel_rfl

/-- Every unified query retains the complete public CSR decoder row. -/
theorem unified_query_check : (List.range 10).all (fun index => decide (
    (FamilyCallers.Block.callerRow .blakeRound 0 4 0 index).decoderQuery =
      ((entry .unified (BitVec.ofNat 32 (4 * index))).data.row
        (BitVec.ofNat 32 (4 * index))).map (fun value : Nat => (value : ZMod babyBearModulus)))) = true := by
  kernel_rfl

/-- Each unrolled row is a member of its actual public program. -/
theorem unrolled_decoded : ∀ row ∈ unrolledTrace.rows,
    Decoded (.pooled row.family) row.decoderQuery unrolledProgram := by
  intro row member
  obtain ⟨index, bound, rfl⟩ := unrolled_mem_rows member
  refine ⟨entry (.pooled .addSub) (BitVec.ofNat 32 (4 * index)), ?_, rfl, ?_⟩
  · apply List.mem_map_of_mem
    change BitVec.ofNat 32 (4 * index) ∈ (List.range 10).map (fun index => BitVec.ofNat 32 (0 + 4 * index))
    simp only [Nat.zero_add]
    exact List.mem_map_of_mem (List.mem_range.mpr bound)
  · exact of_decide_eq_true (List.all_eq_true.mp unrolled_query_check index (List.mem_range.mpr bound))

/-- Each unified row is a member of the same public instruction sequence. -/
theorem unified_decoded : ∀ row ∈ unifiedTrace.rows,
    Decoded .unified row.decoderQuery unifiedProgram := by
  intro row member
  obtain ⟨index, bound, rfl⟩ := FamilyCallers.Block.mem_rows member
  refine ⟨entry .unified (BitVec.ofNat 32 (4 * index)), ?_, rfl, ?_⟩
  · apply List.mem_map_of_mem
    change BitVec.ofNat 32 (4 * index) ∈ (List.range 10).map (fun index => BitVec.ofNat 32 (0 + 4 * index))
    simp only [Nat.zero_add]
    exact List.mem_map_of_mem (List.mem_range.mpr bound)
  · exact of_decide_eq_true (List.all_eq_true.mp unified_query_check index (List.mem_range.mpr bound))

end Airbender.NonVacuous.RoundWindow
