import Airbender.Review.Circuits.ReducedMachine.PhysicalDecoderSetup
import Airbender.Proofs.Tables.NormalizeLast
import Airbender.Proofs.ReducedMachine.NativeDecoderTableArguments
import Airbender.Proofs.ReducedMachine.NativeUnifiedDecoder

namespace Airbender.ReducedMachine.NativePhysicalDecoderSetupProofs
open Native Trace NativePhysicalDecoderSetup NativeDecoderTableArguments NativeDecoderArguments
open Airbender.Trace.Proofs
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

theorem physical_geometry : decoderTableLayout.traceLength = 8388608 ∧
    decoderTableLayout.setupStart = 6 ∧ decoderTableLayout.setupWidth = 16 ∧
    decoderTableLayout.decoderCapacity = 1048576 := by decide +kernel

theorem slice_row {Kind : Type} (setup : SparseDecoderSetup Kind) (i : Nat) (bound : i < sliceSize setup) :
    ordinaryRow setup i = setup.row ⟨i,bound⟩ := dif_pos bound

theorem tail_row {Kind : Type} (setup : SparseDecoderSetup Kind) (i : Nat) (tail : sliceSize setup ≤ i) :
    ordinaryRow setup i = Vector.replicate 10 (-1) := dif_neg (by omega)

theorem normalized_ordinary {Kind : Type} (setup : SparseDecoderSetup Kind) (i : Nat)
    (ordinary : i < decoderTableLayout.traceLength-1) : normalizedRow setup i = ordinaryRow setup i := by
  apply Vector.ext
  intro column small
  simp only [normalizedRow,Verification.normalizeRows,Vector.getElem_ofFn]
  exact Verification.NormalizeLastProofs.ordinary _ ordinary

theorem normalized_terminal {Kind : Type} (setup : SparseDecoderSetup Kind) (column : Fin 10) :
    (normalizedRow setup (decoderTableLayout.traceLength-1))[column.val] =
      -(∑ i ∈ Finset.range (decoderTableLayout.traceLength-1), (ordinaryRow setup i)[column.val]) :=
  Verification.NormalizeLastProofs.vector_terminal decoderTableLayout.traceLength (ordinaryRow setup) column

theorem normalized_sum {Kind : Type} (setup : SparseDecoderSetup Kind) (column : Fin 10) :
    (∑ i ∈ Finset.range decoderTableLayout.traceLength, (normalizedRow setup i)[column.val]) = 0 :=
  Verification.NormalizeLastProofs.vector_sum (size := decoderTableLayout.traceLength) (by decide)
    (ordinaryRow setup) column

theorem bound_main {Kind R : Type} [Field R] (setup : SparseDecoderSetup Kind) (proof : Proof R) :
    (withPublicSetup setup proof).main = proof.main := rfl

theorem bound_decoder_query {Kind R : Type} [Field R] (setup : SparseDecoderSetup Kind) (proof : Proof R)
    (i : Nat) : setupQuery (withPublicSetup setup proof) i = normalizedRow setup i := by
  apply Vector.ext
  intro column small
  simp only [setupQuery,Vector.getElem_ofFn,withPublicSetup,setupColumn]
  have inside : decoderTableLayout.setupStart ≤ decoderTableLayout.setupStart+column ∧
      decoderTableLayout.setupStart+column < decoderTableLayout.setupStart+10 := by omega
  rw [dif_pos inside]
  simp only [Nat.add_sub_cancel_left]
  rfl

theorem bound_other_columns {Kind R : Type} [Field R] (setup : SparseDecoderSetup Kind) (proof : Proof R)
    (i : Nat) (column : DecoderSetupColumn)
    (outside : ¬ (decoderTableLayout.setupStart ≤ column.index ∧ column.index < decoderTableLayout.setupStart+10)) :
    (withPublicSetup setup proof).setup i column = proof.setup i column := dif_neg outside

/-- Transfer is DERIVED from each concrete constructed row; no table-equivalence
    premise and no dropping holes or the physical tail. -/
theorem public_member {Kind : Type} {setup : SparseDecoderSetup Kind} {query : Vector F 10}
    (member : (table setup).Contains #[] query) (notPadding : query ≠ Vector.replicate 10 (-1)) :
    setup.table.Contains #[] query := by
  obtain ⟨i,same⟩ := member
  by_cases inside : i.val < sliceSize setup
  · exact ⟨⟨i.val,inside⟩,same.trans (slice_row setup i.val inside)⟩
  · have tail := tail_row setup i.val (Nat.le_of_not_gt inside)
    exact (notPadding (same.trans tail)).elim

private theorem mapM_length {α β : Type} (f : α → Option β) {xs : List α} {ys : List β}
    (built : xs.mapM f = some ys) : ys.length = xs.length := by
  induction xs generalizing ys with
  | nil => simp [List.mapM_nil,pure] at built; subst ys; rfl
  | cons x xs ih =>
    rw [List.mapM_cons] at built
    cases first : f x with
    | none => simp [first,bind,Option.bind] at built
    | some y =>
      cases rest : xs.mapM f with
      | none => simp [first,rest,bind,Option.bind] at built
      | some tail =>
        simp only [first,rest,bind,Option.bind,pure,Option.some.injEq] at built
        subst ys
        simpa only [List.length_cons] using congrArg Nat.succ (ih rest)

theorem public_extent {Kind : Type} {projection : SailRV32.instruction → Option (DecoderData Kind)}
    {before : Reference.RiscV.Sail.State} {count logCapacity : Nat} {setup : SparseDecoderSetup Kind}
    (image : sparseDecoderSetupImageRunWith projection before count logCapacity = some setup) :
    sliceSize setup = 2 ^ logCapacity := by
  unfold sparseDecoderSetupImageRunWith at image
  split at image
  · rename_i fits
    cases slots : ((List.range count).map fun i => BitVec.ofNat 32 (4 * i)).mapM
        (programSlotRunWith projection before) with
    | none => simp [slots] at image
    | some entries =>
      simp only [slots,bind,Option.bind,pure,Option.some.injEq] at image
      subst setup
      have length := mapM_length _ slots
      simp only [List.length_map,List.length_range] at length
      simp only [sliceSize]
      omega
  · cases image

theorem unified_source {w : Nat → F} {setup : SparseDecoderSetup UnifiedMode}
    {before : Reference.RiscV.Sail.State} {count : Nat} {fixed : Table F (fields 4)}
    (image : unifiedDecoderSetupImage before count 20 = some setup)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints fixed))
    (member : (table setup).Contains #[] (decoderQuery w)) :
    sliceSize setup = decoderTableLayout.decoderCapacity ∧
      ∃ entry ∈ setup.program, entry.SourceWith before unifiedDecoderFields ∧ decoderQuery w = entry.query := by
  refine ⟨public_extent image,?_⟩
  exact NativeUnifiedDecoderProofs.fetched_sources image holds
    (public_member member (NativeShiftDecoderProofs.padding_excluded holds))
theorem public_tail {Kind : Type} {projection : SailRV32.instruction → Option (DecoderData Kind)}
    {before : Reference.RiscV.Sail.State} {count : Nat} {setup : SparseDecoderSetup Kind}
    (image : sparseDecoderSetupImageRunWith projection before count 20 = some setup)
    (i : Nat) (tail : decoderTableLayout.decoderCapacity ≤ i) :
    ordinaryRow setup i = Vector.replicate 10 (-1) := by
  have extent : sliceSize setup = decoderTableLayout.decoderCapacity := public_extent image
  exact tail_row setup i (by rw [extent]; exact tail)

theorem constructed_arguments {Kind Setup R : Type} [Field R]
    (setup : SparseDecoderSetup Kind) (embed : F →+* R) (memory : Airbender.Blake2Worker.Native.MemoryKeyChallenges R)
    (ch : CSRArgumentChallenges R) (pc : NativeMemoryBoundary.PCChallenges R) (decoder : Challenges R)
    (config : Airbender.Blake2Worker.Native.WorkerConfiguration Setup) {proofs : List (Proof R)}
    {batch : Airbender.Blake2Worker.Native.WorkerBatch Setup R} {inputs : NativeMemoryBoundary.PublicBoundary}
    {inverse : NativeMemoryBoundary.BoundaryInverses R}
    (accepted : NativeDecoderTableArguments.Accepted embed memory ch pc decoder config
      (proofs.map (withPublicSetup setup)) batch inputs inverse) :
    NativeMainArguments.Effects embed memory pc (proofs.map Proof.main) batch inputs ∧
      ∀ proof ∈ proofs, auxiliarySum proof true = auxiliarySum proof false ∧
        ∀ i < decoderTableLayout.traceLength-1, setupQuery (withPublicSetup setup proof) i = ordinaryRow setup i := by
  have previous := NativeDecoderTableArgumentProofs.joint_effects embed memory ch pc decoder config accepted
  refine ⟨?_,?_⟩
  · simpa only [List.map_map,Function.comp_def,withPublicSetup] using previous.1
  · intro proof member
    have mapped : withPublicSetup setup proof ∈ proofs.map (withPublicSetup setup) := List.mem_map.mpr ⟨proof,member,rfl⟩
    refine ⟨previous.2 (withPublicSetup setup proof) mapped,?_⟩
    intro i ordinary
    exact (bound_decoder_query setup proof i).trans (normalized_ordinary setup i ordinary)
end Airbender.ReducedMachine.NativePhysicalDecoderSetupProofs
