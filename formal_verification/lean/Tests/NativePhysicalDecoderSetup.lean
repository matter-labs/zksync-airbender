import Tests.NativePhysicalDecoderSetupBase

namespace Airbender.Tests.NativePhysicalDecoderSetup
open Airbender.ReducedMachine Airbender.ReducedMachine.Native Airbender.Trace
open Airbender.ReducedMachine.NativePhysicalDecoderSetup Airbender.ReducedMachine.NativeDecoderTableArguments
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

/-- Metadata/reference data only, with a hole retained before the entry. -/
def holeSetup (entry : UnifiedProgramEntry) : SparseDecoderSetup UnifiedMode := ⟨[none,some entry],0⟩

theorem holes_and_original_slot (entry : UnifiedProgramEntry) :
    ordinaryRow (holeSetup entry) 0 = Vector.replicate 10 (-1) ∧
    ordinaryRow (holeSetup entry) 1 = entry.query := by
  constructor
  · rw [NativePhysicalDecoderSetupProofs.slice_row (holeSetup entry) 0 (by simp only [sliceSize,holeSetup,List.length_cons,List.length_nil]; omega)]
    rfl
  · rw [NativePhysicalDecoderSetupProofs.slice_row (holeSetup entry) 1 (by simp only [sliceSize,holeSetup,List.length_cons,List.length_nil]; omega)]
    rfl

theorem hole_slice_tail (entry : UnifiedProgramEntry) :
    ordinaryRow (holeSetup entry) 2 = Vector.replicate 10 (-1) :=
  NativePhysicalDecoderSetupProofs.tail_row (holeSetup entry) 2
    (by simp only [sliceSize,holeSetup,List.length_cons,List.length_nil]; omega)

theorem physical_entry_member (entry : UnifiedProgramEntry) :
    (table (holeSetup entry)).Contains #[] entry.query :=
  ⟨⟨1,by change 1 < 8388607; omega⟩,(holes_and_original_slot entry).2.symm⟩

theorem physical_outer_tail (entry : UnifiedProgramEntry) :
    ordinaryRow (holeSetup entry) 8388606 = Vector.replicate 10 (-1) :=
  NativePhysicalDecoderSetupProofs.tail_row (holeSetup entry) 8388606
    (by simp only [sliceSize,holeSetup,List.length_cons,List.length_nil]; omega)

theorem constructed_queries (i : Nat) (ordinary : i < decoderTableLayout.traceLength-1) :
    setupQuery (withPublicSetup emptySetup NativeDecoderTable.observed) i = Vector.replicate 10 (-1) := by
  have normalized := NativePhysicalDecoderSetupProofs.bound_decoder_query emptySetup NativeDecoderTable.observed i
  have actual := NativePhysicalDecoderSetupProofs.normalized_ordinary emptySetup i ordinary
  exact normalized.trans (actual.trans (empty_ordinary i))

theorem retain_nondecoder_columns (i : Nat) :
    (withPublicSetup emptySetup NativeDecoderTable.observed).setup i ⟨2⟩ =
      NativeDecoderTable.observed.setup i ⟨2⟩ :=
  NativePhysicalDecoderSetupProofs.bound_other_columns emptySetup NativeDecoderTable.observed i ⟨2⟩
    (by change ¬ (6 ≤ 2 ∧ 2 < 16); decide +kernel)

theorem retain_body_and_auxiliary :
    (withPublicSetup emptySetup NativeDecoderTable.observed).main = NativeDecoderTable.observed.main := rfl


/-- No complete native body can query the constructed empty ordinary table.
    Normalized last-row data is deliberately absent from this lookup boundary. -/
theorem empty_table_rejected {fixed : Table F (fields 4)} {w : Nat → F}
    (holds : FlatOperation.ConstraintsHoldFlat (Airbender.Verification.environment w) (importedConstraints fixed)) :
    ¬ (table emptySetup).Contains #[] (decoderQuery w) := by
  intro member
  obtain ⟨i,same⟩ := member
  exact NativeShiftDecoderProofs.padding_excluded holds (same.trans (empty_ordinary i.val))
end Airbender.Tests.NativePhysicalDecoderSetup
