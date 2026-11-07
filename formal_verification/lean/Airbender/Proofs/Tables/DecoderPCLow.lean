import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Proofs.Trace.PC
import Airbender.Review.Helpers.Decoder.PooledProgram
import Airbender.Proofs.JumpBranchSlt.PCState
import Airbender.Proofs.MulDiv
import Airbender.Proofs.ShiftBinop
import Airbender.Proofs.SubwordMemory
import Airbender.Proofs.UnifiedReduced
import Airbender.Review.Helpers.UnifiedReduced.Registry

namespace Airbender.Trace.NativeDecoder.Proofs
open Arithmetic
set_option warningAsError true
set_option Elab.async false

/-- The guarded decoder limb is independently ranged on every native outgoing
    PC. This uses the low limb only and preserves the noncanonical high-PC case. -/
theorem pooled_final_pc_low [Fact p.Prime] (hp : FieldCapacity.NativeRomCapacity p)
    (row : Row p PooledFamily) (setup : PooledSetup p)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment)
      (row.constraints setup)) : row.finish.word.lo < limbBase := by
  cases row with
  | mk family w =>
    cases family with
    | addSub =>
      have core := Verification.holds_of_sublist holds
        (List.sublist_append_left AddSub.importedConstraints AddSub.importedConstraintsTimestampLookups)
      have actual := AddSub.Proofs.pc_bounds core
        (initial := ⟨(w 0).val, (w 1).val⟩) (final := ⟨(w 19).val, (w 20).val⟩)
        ⟨(ZMod.natCast_zmod_val _).symm, (ZMod.natCast_zmod_val _).symm, rfl, rfl⟩
      exact actual.1
    | wordMemory =>
      have core := Verification.holds_of_sublist holds
        (List.sublist_append_left (WordMemory.importedConstraints setup.wordMemory)
          WordMemory.importedConstraintsTimestampLookups)
      exact (WordMemory.Proofs.local_ranges core).2.1
    | jumpBranchSlt =>
      have core := Verification.holds_of_sublist holds
        (List.sublist_append_left JumpBranchSlt.importedConstraints JumpBranchSlt.importedConstraintsTimestampLookups)
      exact JumpBranchSlt.Proofs.final_pc_low_bound hp core
    | mulDiv =>
      have core := Verification.holds_of_sublist holds
        (List.sublist_append_left MulDiv.importedConstraints MulDiv.importedConstraintsTimestampLookups)
      exact MulDiv.Proofs.local_ranges core ⟨6, by decide⟩
    | shiftBinop =>
      have core := Verification.holds_of_sublist holds
        (List.sublist_append_left ShiftBinop.importedConstraints ShiftBinop.importedConstraintsTimestampLookups)
      exact (ShiftBinop.Proofs.local_ranges core).1
    | subwordMemory =>
      have core := Verification.holds_of_sublist holds
        (List.sublist_append_left (SubwordMemory.importedConstraints setup.subwordMemory)
          SubwordMemory.importedConstraintsTimestampLookups)
      exact (SubwordMemory.Proofs.local_ranges core).2.2.2.1

/-- Accepted raw state matching transports the independently ranged outgoing
    limbs and the public initial PC to every incoming decoder query. Filler
    exclusion therefore needs no per-row typed-limb assumption. -/
theorem pooled_query_pc_low [Fact p.Prime] (hp : FieldCapacity.NativeRomCapacity p)
    {trace : PooledTrace p} (accepted : Accepted trace)
    (initial : trace.initial.word.lo < limbBase) :
    ∀ row ∈ trace.rows, row.decoderQuery[0].val < 65536 := by
  have typed := Trace.Proofs.matched_incoming_property accepted
    (fun state => state.word.lo < limbBase) initial
    (fun row member => pooled_final_pc_low hp row trace.rom (accepted.constraints row member))
  intro row member
  have actual := typed row.start
    (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨row, member, rfl⟩))
  cases row with
  | mk family w =>
    cases family <;> change (w 0).val < 65536 at actual ⊢
    all_goals exact actual

theorem unified_query_pc_low [Fact p.Prime] {trace : UnifiedTrace p}
    (accepted : Accepted trace) (initial : trace.initial.word.lo < limbBase) :
    ∀ row ∈ trace.rows, row.decoderQuery[0].val < 65536 := by
  have outputs (row : Row p UnifiedFamily) (member : row ∈ trace.rows) :
      row.finish.word.lo < limbBase := by
    have holds := accepted.constraints row member
    cases row with
    | mk family w =>
      cases family
      have core := Verification.holds_of_sublist holds
        (List.sublist_append_left (UnifiedReduced.importedConstraints trace.rom)
          UnifiedReduced.importedConstraintsTimestampLookups)
      exact (UnifiedReduced.Proofs.pc_bounds core).1
  have typed := Trace.Proofs.matched_incoming_property accepted
    (fun state => state.word.lo < limbBase) initial outputs
  intro row member
  have actual := typed row.start
    (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨row, member, rfl⟩))
  cases row with
  | mk family w =>
    cases family
    change (w 0).val < 65536 at actual ⊢
    exact actual

end Airbender.Trace.NativeDecoder.Proofs
