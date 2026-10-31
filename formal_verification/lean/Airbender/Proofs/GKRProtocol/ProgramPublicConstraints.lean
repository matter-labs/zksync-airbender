import Airbender.Proofs.GKRProtocol.ProgramPublicRows
import Airbender.Proofs.GKRProtocol.ProgramConstraintsNative.ShiftBinopUncached
import Airbender.Proofs.GKRProtocol.ProgramConstraintsNative.ShiftBinopCached
import Airbender.Proofs.GKRProtocol.ProgramConstraintsNative.WordMemoryUncached
import Airbender.Proofs.GKRProtocol.ProgramConstraintsNative.WordMemoryCached

namespace Airbender.Compiler.PooledExecution
open Airbender Airbender.Compiler Airbender.Trace Airbender.Trace.NativeDecoder NativeProgramSetup
set_option warningAsError true
set_option Elab.async false

/-- Every unrolled native row satisfies the setup built from public program bytes. -/
theorem ProgramLogicalRowCertificate.program_constraints
    {config : ProgramRows.Config} {initial : Reference.RiscV.Sail.State}
    {text : List (BitVec 32)} {capacity : Nat} {masks : PooledFamily → ProgramRows.Mask}
    {columns : PooledFamily → List (List Source.BaseField)}
    (setup : UnrolledProgramSetup config initial text capacity masks columns)
    {cells : List Cell} {tokens : List (MemoryToken babyBearModulus)}
    (image : initialImage initial cells = some tokens)
    (domain : ROMNative.WordFullPublic.CoversROM cells)
    (cert : ProgramLogicalRowCertificate (unrolledProgramLookupRows initial columns))
    (typed : cert.row.decoderQuery[0].val < 65536) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment cert.row.assignment)
      (cert.row.constraints (⟨ROM.table cells tokens,
        Verification.subwordTable (ROM.words initial)⟩ : PooledSetup babyBearModulus)) := by
  cases cert with
  | addSubUncached input arguments =>
    exact ProgramConstraintsNative.AddSubUncached.input_constraints (unrolledDecoderColumns columns) (ROM.words initial) input arguments _
  | addSubCached input arguments =>
    exact ProgramConstraintsNative.AddSubCached.input_constraints (unrolledDecoderColumns columns) (ROM.words initial) input arguments _
  | jumpBranchUncached input arguments =>
    exact ProgramConstraintsNative.JumpBranchUncached.input_constraints (unrolledDecoderColumns columns) (ROM.words initial) input arguments _
  | jumpBranchCached input arguments =>
    exact ProgramConstraintsNative.JumpBranchCached.input_constraints (unrolledDecoderColumns columns) (ROM.words initial) input arguments _
  | mulDivUncached input arguments =>
    exact ProgramConstraintsNative.MulDivUncached.input_constraints (unrolledDecoderColumns columns) (ROM.words initial) input arguments _
  | mulDivCached input arguments =>
    exact ProgramConstraintsNative.MulDivCached.input_constraints (unrolledDecoderColumns columns) (ROM.words initial) input arguments _
  | shiftBinopUncached input arguments =>
    exact ProgramConstraintsNative.ShiftBinopUncached.input_constraints setup input arguments typed _
  | shiftBinopCached input arguments =>
    exact ProgramConstraintsNative.ShiftBinopCached.input_constraints setup input arguments typed _
  | wordMemoryUncached input arguments =>
    exact ProgramConstraintsNative.WordMemoryUncached.input_constraints (unrolledDecoderColumns columns) input arguments image domain _
  | wordMemoryCached input arguments =>
    exact ProgramConstraintsNative.WordMemoryCached.input_constraints (unrolledDecoderColumns columns) input arguments image domain _
  | subwordMemoryUncached input arguments =>
    exact ProgramConstraintsNative.SubwordMemoryUncached.input_constraints (unrolledDecoderColumns columns) (ROM.words initial) input arguments _
  | subwordMemoryCached input arguments =>
    exact ProgramConstraintsNative.SubwordMemoryCached.input_constraints (unrolledDecoderColumns columns) (ROM.words initial) input arguments _

/-- Exact state matching supplies the PC bounds for all public row constraints. -/
theorem program_row_constraints_from_native
    {config : ProgramRows.Config} {initial : Reference.RiscV.Sail.State}
    {text : List (BitVec 32)} {capacity : Nat} {masks : PooledFamily → ProgramRows.Mask}
    {columns : PooledFamily → List (List Source.BaseField)}
    (setup : UnrolledProgramSetup config initial text capacity masks columns)
    {cells : List Cell} {tokens : List (MemoryToken babyBearModulus)}
    (image : initialImage initial cells = some tokens)
    (domain : ROMNative.WordFullPublic.CoversROM cells)
    (certs : List (ProgramLogicalRowCertificate (unrolledProgramLookupRows initial columns)))
    (trace : PooledTrace babyBearModulus)
    (rowsEq : trace.rows = certs.map ProgramLogicalRowCertificate.row)
    (states : (trace.initial :: trace.rows.map Row.finish).Perm
      (trace.terminal :: trace.rows.map Row.start))
    (initialBound : trace.initial.word.lo < 65536) :
    ∀ row ∈ trace.rows,
      FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment)
        (row.constraints (⟨ROM.table cells tokens,
          Verification.subwordTable (ROM.words initial)⟩ : PooledSetup babyBearModulus)) := by
  have ranges := program_native_query_pc_low (unrolledDecoderColumns columns) (ROM.words initial)
    certs trace rowsEq states initialBound
  intro row member
  have certified : row ∈ certs.map ProgramLogicalRowCertificate.row := rowsEq ▸ member
  obtain ⟨cert, _, rfl⟩ := List.mem_map.mp certified
  exact cert.program_constraints setup image domain (ranges cert.row member)

end Airbender.Compiler.PooledExecution
