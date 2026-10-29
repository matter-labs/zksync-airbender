import Airbender.Proofs.GKRProtocol.PublicNativeRows
import Airbender.Proofs.Tables.DecoderPCLow

namespace Airbender.Compiler
open Airbender.Trace Airbender.Trace.NativeDecoder Reference.RiscV.Sail
set_option warningAsError true
variable [Fact babyBearModulus.Prime]

/-- Imported constraints, state matching and the public initial PC bound give
the low-limb range for every unrolled row. Exact decoder matching then yields
the ordinary/caller distinction without the retained decoder program. Native
acceptance is a lower-level premise here; a top theorem must derive it from
each compiled circuit certificate and explicit logical permutations. -/
theorem unrolled_accepted_row_cases
    {config : ProgramRows.Config} {initial : State} {text : List (BitVec 32)}
    {capacity : Nat} {masks : PooledFamily → ProgramRows.Mask}
    {columns : PooledFamily → List (List (ZMod babyBearModulus))}
    (setup : UnrolledProgramSetup config initial text capacity masks columns)
    {trace : PooledTrace babyBearModulus}
    (lookup : UnrolledDecoderExactLookup trace masks columns)
    (native : Accepted trace)
    (initialBound : trace.initial.word.lo < Arithmetic.limbBase) :
    ∀ row ∈ trace.rows,
      (∃ entry ∈ ProgramRows.programOf config initial text,
        entry.SourceWith initial config.fields ∧ entry.data.family = row.family ∧
          ProgramRows.maskRow (masks row.family) row.decoderQuery =
            ProgramRows.maskRow (masks row.family) entry.query) ∨
      (∃ caller ∈ ProgramRows.callerProgramOf config initial text,
        caller.Source initial config.delegationCSR ∧ row.family = .addSub ∧
          ProgramRows.maskRow (masks row.family) row.decoderQuery =
            ProgramRows.maskRow (masks row.family) caller.query) := by
  have typed := NativeDecoder.Proofs.pooled_query_pc_low (by decide +kernel)
    native initialBound
  intro row member
  exact unrolled_native_row_case setup lookup row member (typed row member)

/-- The same accepted-row classification for the unified circuit. -/
theorem unified_accepted_row_cases
    {initial : State} {text : List (BitVec 32)} {capacity : Nat}
    {mask : ProgramRows.Mask}
    {columns : List (List (ZMod babyBearModulus))}
    (setup : UnifiedProgramSetup initial text capacity mask columns)
    {trace : UnifiedTrace babyBearModulus}
    (lookup : UnifiedDecoderExactLookup trace mask columns)
    (native : Accepted trace)
    (initialBound : trace.initial.word.lo < Arithmetic.limbBase) :
    ∀ row ∈ trace.rows,
      (∃ ordinary ∈ UnifiedProgramRows.ordinaryProgramOf initial text,
        ordinary.SourceWith initial UnifiedProgramRows.decoderFields ∧
          ProgramRows.maskRow mask row.decoderQuery =
            ProgramRows.maskRow mask ordinary.query) ∨
      (∃ caller ∈ UnifiedProgramRows.callerProgramOf initial text,
        caller.Source initial UnifiedProgramRows.delegationCSR ∧
          ProgramRows.maskRow mask row.decoderQuery =
            ProgramRows.maskRow mask caller.query) := by
  have typed := NativeDecoder.Proofs.unified_query_pc_low native initialBound
  intro row member
  exact unified_native_row_case setup lookup row member (typed row member)

end Airbender.Compiler
