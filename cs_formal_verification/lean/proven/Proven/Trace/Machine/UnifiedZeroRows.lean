module
public import Proven.Trace.Machine.ExtraUnifiedZero
public import Human.Trace.Machine.Model

@[expose] public section
namespace Airbender.Trace.Machine.Proofs
open Arithmetic Trace.Proofs
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

/-- Every unified row outside the caller path preserves x0 under its public decoder metadata. -/
theorem unified_noncaller_zero {trace : UnifiedTrace babyBearModulus}
    {row : Trace.Row babyBearModulus UnifiedFamily} {entry : RVMachineProgramEntry} {instruction : RV.Instr}
    (constraints : FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment) (row.constraints trace.rom))
    (active : row.assignment row.columns.execute = 1)
    (fields : rvMachineDecoderFields .unified instruction = some entry.data)
    (query : row.decoderQuery = (entry.data.row entry.pc).map (fun value : Nat => (value : ZMod babyBearModulus)))
    (notCaller : ¬ UnifiedReduced.Caller.Selected row.assignment) : RowZeroPreserving row := by
  obtain ⟨kind, w⟩ := row
  cases kind
  have core := Verification.holds_of_sublist constraints
    (List.sublist_append_left (UnifiedReduced.importedConstraints trace.rom)
      UnifiedReduced.importedConstraintsTimestampLookups)
  rcases machine_fields_cases fields with extra | ⟨_, ordinary, projected, same⟩ | ⟨impossible, _⟩
  · exact extra_unified_zero core active extra query notCaller
  · let native : RVProgramEntry UnifiedFamily := ⟨entry.pc, entry.bits, ordinary⟩
    have nativeQuery : UnifiedReduced.decoderQuery w = native.query := by
      rw [same] at query
      exact query.trans (ordinary_query (fun _ => .unified) native)
    exact UnifiedReduced.Proofs.RV.rv_row_zero_preserving (by decide) core active projected nativeQuery
  · exact False.elim (impossible rfl)

end Airbender.Trace.Machine.Proofs
