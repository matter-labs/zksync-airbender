import Airbender.Review.Circuits.ShiftBinop.SourcesModel
import Airbender.Proofs.Trace.Families.ShiftBinop.Values

namespace Airbender.ShiftBinop.Proofs
open Arithmetic Trace Verification
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- Internal bounded-source lifting of every actual native packed key. -/
theorem shift_source_binding {w : Nat → ZMod mersenne31Modulus} {kind : ShiftKind}
    (contributions : ShiftContributions w kind) (source : (left w).Bounded) :
    ShiftSourceBinding w kind := by
  have amount : (w 29).val < 32 := by rw [contributions.amount]; exact Nat.mod_lt _ (by decide)
  have sourceColumn (slot : Fin 3) : (w (kind.sourceColumn slot)).val < 65536 := by
    cases kind <;> simp only [ShiftKind.sourceColumn]
    all_goals split <;> first | exact source.1 | exact source.2
  have canonical (slot : Fin 3) (active : kind.parts[slot.val] ≠ .zero) :
      (w (43 + 4 * slot.val)).val = (w (kind.sourceColumn slot)).val + 65536 * (w 29).val ∧
      (w (43 + 4 * slot.val)).val % 65536 = (w (kind.sourceColumn slot)).val ∧
      (w (43 + 4 * slot.val)).val / 65536 = (w 29).val :=
    canonical_shift_key _ _ _ (sourceColumn slot) amount (by
      simpa only [active,if_false] using contributions.keys slot)
  refine ⟨source,shift_selected_bounds contributions source,contributions.amount,?_,
    fun slot active => (canonical slot active).2.1,
    fun slot active => (canonical slot active).2.2⟩
  intro slot
  by_cases zero : kind.parts[slot.val] = .zero
  · have key := contributions.keys slot
    simp only [zero,if_true] at key ⊢
    rw [key]
    rfl
  · simpa only [zero,if_false] using (canonical slot zero).1

/-- Native history supplies the source range; original public decoding selects
    each actual shift kind. No source/key/selected bound is a premise. -/
theorem image_shift_sources {trace : Data mersenne31Modulus ShiftBinopFamily}
    {setup : SparseDecoderSetup Operation} {before : Reference.RiscV.Sail.State} {cells : List Cell}
    {count logCapacity : Nat}
    (image : sparseDecoderSetupImage before count logCapacity = some setup)
    (inputs : ImageBoundary trace before cells) (accepted : Accepted trace)
    (decoded : Decoded trace setup) (row : Row mersenne31Modulus ShiftBinopFamily)
    (present : row ∈ trace.rows) :
    ∃ entry ∈ setup.program, entry.SourceWith before decoderFields ∧
      row.decoderQuery = entry.query ∧
      ∀ kind, entry.data.family = kind.operation → ShiftSourceBinding row.assignment kind := by
  have bounds := (image_value_bounds image inputs accepted decoded).1 row present
    importedConstraintsMemoryPorts[0] (by
      cases row with
      | mk family w => cases family; change _ ∈ importedConstraintsMemoryPorts; simp [importedConstraintsMemoryPorts])
  have native := accepted.constraints row present
  have member := decoded row present
  rw [row_decoder_query] at member
  cases row with
  | mk family w =>
    cases family
    rw [Airbender.Trace.Proofs.read_word] at bounds
    change (left w).Bounded at bounds
    obtain ⟨entry,found,source,query⟩ := fetched_sources image native member
    exact ⟨entry,found,source,query,fun kind family =>
      shift_source_binding (entry_shift_contributions native source.fields query kind family) bounds⟩

end Airbender.ShiftBinop.Proofs
