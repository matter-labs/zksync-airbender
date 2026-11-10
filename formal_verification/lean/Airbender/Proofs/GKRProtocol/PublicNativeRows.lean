import Airbender.Proofs.GKRProtocol.PublicProgramCases

namespace Airbender.Compiler
open Airbender.Trace Airbender.Trace.NativeDecoder Reference.RiscV.Sail
set_option warningAsError true
variable [Fact babyBearModulus.Prime]

/-- Exact lookup matching to the public text-derived setup classifies an
actual unrolled trace row as ordinary or delegated. The mask must be bound
separately to the imported circuit's selected columns. -/
theorem unrolled_native_row_case
    {config : ProgramRows.Config} {initial : State} {text : List (BitVec 32)}
    {capacity : Nat} {masks : PooledFamily → ProgramRows.Mask}
    {columns : PooledFamily → List (List (ZMod babyBearModulus))}
    (setup : UnrolledProgramSetup config initial text capacity masks columns)
    {trace : PooledTrace babyBearModulus}
    (lookup : UnrolledDecoderExactLookup trace masks columns)
    (row : Row babyBearModulus PooledFamily) (rowMember : row ∈ trace.rows)
    (typed : row.decoderQuery[0].val < 65536) :
    (∃ entry ∈ ProgramRows.programOf config initial text,
      entry.SourceWith initial config.fields ∧ entry.data.family = row.family ∧
        ProgramRows.maskRow (masks row.family) row.decoderQuery =
          ProgramRows.maskRow (masks row.family) entry.query) ∨
    (∃ caller ∈ ProgramRows.callerProgramOf config initial text,
      caller.Source initial config.delegationCSR ∧ row.family = .addSub ∧
        ProgramRows.maskRow (masks row.family) row.decoderQuery =
          ProgramRows.maskRow (masks row.family) caller.query) := by
  apply unrolled_active_public_case setup row.family _ (lookup row rowMember)
  simpa [ProgramRows.maskRow] using typed

/-- The same classification for the unified circuit's actual row query. -/
theorem unified_native_row_case
    {initial : State} {text : List (BitVec 32)} {capacity : Nat}
    {mask : ProgramRows.Mask}
    {columns : List (List (ZMod babyBearModulus))}
    (setup : UnifiedProgramSetup initial text capacity mask columns)
    {trace : UnifiedTrace babyBearModulus}
    (lookup : UnifiedDecoderExactLookup trace mask columns)
    (row : Row babyBearModulus UnifiedFamily) (rowMember : row ∈ trace.rows)
    (typed : row.decoderQuery[0].val < 65536) :
    (∃ ordinary ∈ UnifiedProgramRows.ordinaryProgramOf initial text,
      ordinary.SourceWith initial UnifiedProgramRows.decoderFields ∧
        ProgramRows.maskRow mask row.decoderQuery =
          ProgramRows.maskRow mask ordinary.query) ∨
    (∃ caller ∈ UnifiedProgramRows.callerProgramOf initial text,
      caller.Source initial UnifiedProgramRows.delegationCSR ∧
        ProgramRows.maskRow mask row.decoderQuery =
          ProgramRows.maskRow mask caller.query) := by
  apply unified_active_public_case setup _ (lookup row rowMember)
  simpa [ProgramRows.maskRow] using typed

end Airbender.Compiler
