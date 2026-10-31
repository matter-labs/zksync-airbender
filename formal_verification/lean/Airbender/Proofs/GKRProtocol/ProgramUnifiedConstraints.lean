import Airbender.Proofs.GKRProtocol.ProgramPCBounds
import Airbender.Proofs.GKRProtocol.ProgramConstraintsNative.UnifiedUncached
import Airbender.Proofs.GKRProtocol.ProgramConstraintsNative.UnifiedCached

namespace Airbender.Compiler.UnifiedExecution
open Airbender Airbender.Compiler Airbender.Trace Airbender.Trace.NativeDecoder NativeProgramSetup
set_option warningAsError true
set_option Elab.async false

/-- Both unified native profiles satisfy the setup built from public program bytes. -/
theorem ProgramLogicalRowCertificate.program_constraints
    {initial : Reference.RiscV.Sail.State} {text : List (BitVec 32)} {capacity : Nat}
    {mask : ProgramRows.Mask} {columns : List (List Source.BaseField)}
    (setup : UnifiedProgramSetup initial text capacity mask columns)
    (cert : ProgramLogicalRowCertificate (unifiedLookupRows initial columns))
    (typed : cert.row.decoderQuery[0].val < 65536) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment cert.row.assignment)
      (cert.row.constraints (UnifiedReduced.Setup.table initial)) := by
  cases cert with
  | unifiedUncached input arguments =>
    exact ProgramConstraintsNative.UnifiedUncached.input_constraints setup input arguments typed
  | unifiedCached input arguments =>
    exact ProgramConstraintsNative.UnifiedCached.input_constraints setup input arguments typed

/-- Exact state matching derives every incoming PC bound before helper transport. -/
theorem program_row_constraints_from_native
    {initial : Reference.RiscV.Sail.State} {text : List (BitVec 32)} {capacity : Nat}
    {mask : ProgramRows.Mask} {columns : List (List Source.BaseField)}
    (setup : UnifiedProgramSetup initial text capacity mask columns)
    (certs : List (ProgramLogicalRowCertificate (unifiedLookupRows initial columns)))
    (trace : UnifiedTrace babyBearModulus)
    (rowsEq : trace.rows = certs.map ProgramLogicalRowCertificate.row)
    (states : (trace.initial :: trace.rows.map Row.finish).Perm
      (trace.terminal :: trace.rows.map Row.start))
    (initialBound : trace.initial.word.lo < 65536) :
    ∀ row ∈ trace.rows,
      FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment)
        (row.constraints (UnifiedReduced.Setup.table initial)) := by
  have ranges := native_query_pc_low (unifiedDecoderColumns columns) (ROM.words initial)
    certs trace rowsEq states initialBound
  intro row member
  have certified : row ∈ certs.map ProgramLogicalRowCertificate.row := rowsEq ▸ member
  obtain ⟨cert, _, rfl⟩ := List.mem_map.mp certified
  exact cert.program_constraints setup (ranges cert.row member)

end Airbender.Compiler.UnifiedExecution
